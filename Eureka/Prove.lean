import Eureka.Concepts

/-!
# Proof search (DESIGN_PROVE)

Two untrusted hunters above the symbolic ladder, both feeding the same
gate:

* **Repair** (V1, the control): the model sees the closed statement and
  retrieved premises, returns a whole `by`-script; a failing script's
  error text feeds one repair round. The baseline's measured pattern,
  in-process.
* **The stepper** (V3, the wager): search over tactic states — cheap
  moves first, then the model as a *move generator* that sees the
  rendered goal (hypotheses included) and returns one tactic line.
  Ordered depth-first with a node budget and depth cap; success
  extracts the assembled proof term.

Both are LLM-optional (`none` transport = off), both are untrusted:
whatever they find still passes `commitFact` — screen, kernel, axiom
audit. The audit is the script screening: a proof routed through a
minted axiom or a `native_decide` shortcut dies at the gate (V5).
-/

open Lean Meta Elab

namespace Eureka
namespace Runtime

/-- Prose lines open with an uppercase sentence ("Looking at this goal,
I need..."); tactic lines open lowercase or with a symbol. Blank lines
count as prose so leading/trailing paragraphs strip cleanly. -/
private def proseLine (line : String) : Bool :=
  let l := line.trimAscii.toString
  l.isEmpty || l.front.isUpper

/-- Recover the tactic script from model output: unwrap `<answer>` tags
and code fences, strip leading/trailing prose and a leading `by`. -/
def extractProofScript (text : String) : String :=
  let t := text.trimAscii.toString
  let t := match t.splitOn "<answer>" with
    | _ :: rest :: _ =>
      ((rest.splitOn "</answer>").headD rest).trimAscii.toString
    | _ => t
  let t := match t.splitOn "```" with
    | _ :: chunk :: _ =>
      (String.intercalate "\n" ((chunk.splitOn "\n").drop 1)).trimAscii.toString
    | _ => t
  let t :=
    let lines := (t.splitOn "\n").dropWhile proseLine
    let lines := (lines.reverse.dropWhile proseLine).reverse
    if lines.isEmpty then t else String.intercalate "\n" lines
  let t := t.trimAscii.toString
  if t.startsWith "by\n" then (t.drop 3).trimAscii.toString
  else if t.startsWith "by " then (t.drop 3).trimAscii.toString
  else t

def renderProofPrompt (goal premises : String) (lastError : Option String) :
    String :=
  let feedback := match lastError with
    | some e => s!"\nYour previous attempt failed:\n{e}\nFix it.\n"
    | none => ""
  s!"You are the prover in a verified discovery system. Prove this Lean 4 \
theorem; your tactic script is machine-checked by the Lean kernel.

Goal:
  {goal}

Lemmas likely to help (full names, from Mathlib/core):
{premises}{feedback}
Definitions in the `Invented` namespace have no simp lemmas: open them \
with `unfold Invented.foo at h ⊢` or `change`, never `simp [Invented.foo]`.
Reply with ONLY the tactic script (what goes after `by`), no prose, no \
code fences. `sorry`, `admit`, and fresh axioms are rejected."

def renderMovePrompt (goalState premises : String) : String :=
  s!"You are choosing the next tactic in a Lean 4 proof. Current goal \
(with hypotheses):

{goalState}

Lemmas likely to help:
{premises}
Reply with ONE tactic line (a single step, e.g. `induction n`, \
`simp only [Foo.bar]`, `exact Foo.baz h`), no prose, no code fences."

/-- V1: whole-script generation with one error-feedback repair round.
Returns the proof and the number of calls spent. -/
def proveByRepair (call : String → IO (Except String String))
    (known : Array KnownLemma) (stmt : Expr) (rounds : Nat := 2) :
    MetaM (Option (Expr × Nat)) := do
  let premises ← retrievePremises known stmt
  let mut premStr := ""
  for p in premises do
    premStr := premStr ++ s!"  {p.name} : {toString (← ppExpr p.type)}\n"
  let goalStr := toString (← ppExpr stmt)
  let mut lastErr : Option String := none
  for i in [0:rounds] do
    match ← call (renderProofPrompt goalStr premStr lastErr) with
    | .error e =>
      IO.println s!"  [llm-repair] transport failed: {e}"
      return none
    | .ok text =>
      let script := extractProofScript text
      match ← withCurrHeartbeats (tryTacticClosedErr script stmt) with
      | .ok pf => return some (pf, i + 1)
      | .error err =>
        lastErr := some s!"script:\n{script}\nerror: {err}"
  return none

/-- Apply one tactic to one goal: the new goals, or the error. -/
def runMove (g : MVarId) (tacSrc : String) :
    MetaM (Except String (List MVarId)) := do
  match Parser.runParserCategory (← getEnv) `tactic tacSrc with
  | .error e => return .error s!"parse: {e}"
  | .ok stx =>
    let savedMsgs := (← getThe Core.State).messages
    let r ← tryCatchRuntimeEx
      (try
        let (goals, _) ← Term.TermElabM.run' <| withCurrHeartbeats <|
          Elab.runTactic g stx
        pure (Except.ok goals)
      catch ex => do
        pure (Except.error (← ex.toMessageData.toString)))
      (fun _ => pure (.error "runtime blowup"))
    modifyThe Core.State fun st => { st with messages := savedMsgs }
    return r

structure StepperConfig where
  /-- Cheap single-step moves, tried before any LLM call. -/
  moves : Array String :=
    #["intro a", "constructor", "simp_all", "omega"]
  nodeBudget : Nat := 40
  maxDepth : Nat := 6
  /-- Model suggestions taken per stuck goal. -/
  llmMovesPerGoal : Nat := 1
  /-- Total model calls per statement. -/
  llmCallCap : Nat := 6

/-- Ordered depth-first search with backtracking: cheap moves exhaust
first; only a goal no cheap move advances consults the model. -/
partial def stepperGo (cfg : StepperConfig) (known : Array KnownLemma)
    (call? : Option (String → IO (Except String String)))
    (nodes llmCalls : IO.Ref Nat) (depth : Nat) (goals : List MVarId) :
    MetaM Bool := do
  match goals with
  | [] => return true
  | g :: rest =>
    if depth ≥ cfg.maxDepth then return false
    for phase in [0, 1] do
      let cand ← do
        if phase == 0 then pure cfg.moves
        else match call? with
          | none => pure #[]
          | some call =>
            if (← llmCalls.get) ≥ cfg.llmCallCap then pure #[]
            else do
              llmCalls.modify (· + 1)
              let gStr := toString (← Meta.ppGoal g)
              let premises ← retrievePremises known (← g.getType)
              let mut premStr := ""
              for p in premises do
                premStr := premStr ++ s!"  {p.name} : {toString (← ppExpr p.type)}\n"
              match ← call (renderMovePrompt gStr premStr) with
              | .ok text =>
                pure <| ((extractProofScript text).splitOn "\n").toArray
                  |>.map (·.trimAscii.toString)
                  |>.filter (fun l => !l.isEmpty)
                  |>.extract 0 cfg.llmMovesPerGoal
              | .error _ => pure #[]
      for mv in cand do
        if (← nodes.get) ≥ cfg.nodeBudget then return false
        nodes.modify (· + 1)
        let s ← saveState
        match ← runMove g mv with
        | .ok newGoals =>
          if ← stepperGo cfg known call? nodes llmCalls (depth + 1)
              (newGoals ++ rest) then
            return true
          s.restore
        | .error _ => s.restore
    return false

/-- V3: prove `stmt` by tactic-state search. The proof term is assembled
from the search's assignments and, as always, is untrusted until the
gate says otherwise. -/
def proveByStepper (call? : Option (String → IO (Except String String)))
    (known : Array KnownLemma) (stmt : Expr)
    (cfg : StepperConfig := {}) : MetaM (Option Expr) := do
  let r ← attempt do
    let goalMVar ← mkFreshExprMVar stmt
    let nodes ← IO.mkRef 0
    let llmCalls ← IO.mkRef 0
    if ← stepperGo cfg known call? nodes llmCalls 0 [goalMVar.mvarId!] then
      let pf ← instantiateMVars goalMVar
      if pf.hasSorry || pf.hasExprMVar then pure none
      else pure (some pf)
    else
      pure none
  return r.join

end Runtime
end Eureka
