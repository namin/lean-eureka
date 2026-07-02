import Eureka.Loop
import Eureka.LLM

/-!
# The proposal booth

Stage one of the LLM proposer: the model sees the corpus and the outcomes of
its previous round (admitted, refuted with counterexamples, aliases,
unparseable lines) and proposes conjectures as bare Lean terms, one per
line. Each line must survive, in order: parsing, elaboration at type `Prop`,
deduplication (verbatim and definitional), counterexample search, the
evidence hunt, and the gate. The LLM is a proposer exactly like the
template heuristics — smarter, and no more trusted.

The transport is a parameter (`call`), so the pipeline runs deterministically
under test (`BoothStub.lean`) and against Bedrock in `BoothRun.lean`.
-/

open Lean Meta Elab

namespace Eureka
namespace Runtime

/-- Outcomes of one booth round, fed back into the next round's prompt. -/
structure BoothLog where
  admitted : Array String := #[]
  refuted : Array (String × String) := #[]
  merged : Array (String × Name) := #[]
  dups : Array String := #[]
  «open» : Array String := #[]
  unparseable : Array String := #[]

/-- Parse and elaborate one proposed line at type `Prop`. Everything about
the result is re-checked downstream; this is convenience, not trust. -/
def parseConjecture (s : String) : MetaM (Option Expr) := do
  match Parser.runParserCategory (← getEnv) `term s with
  | .error _ => return none
  | .ok stx =>
    -- A failed elaboration may *log* errors as well as throw; restore the
    -- message log so a rejected proposal leaves no trace in the file's
    -- diagnostics.
    let savedMsgs := (← getThe Core.State).messages
    let result ← try
        let e ← Term.TermElabM.run' <| Term.withoutErrToSorry do
          let e ← Term.elabTerm stx (some (mkSort .zero))
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
        if e.hasSorry || e.hasMVar || e.hasFVar then pure none
        else if ← isProp e then pure (some e)
        else pure none
      catch _ => pure none
    modifyThe Core.State fun st => { st with messages := savedMsgs }
    return result

/-- Keep the lines that look like proposals: strip list markers and require
a leading `∀`. -/
def extractCandidates (text : String) : List String :=
  text.splitOn "\n"
    |>.map (fun l =>
      ((l.trimAscii.dropWhile fun c =>
        c == '-' || c == '*' || c == '`' || c == '.' || c == ')' || c.isDigit || c == ' ').trimAscii).toString)
    |>.filter (·.startsWith "∀")

def renderLog (log : BoothLog) : String := Id.run do
  let mut s := ""
  unless log.admitted.isEmpty do
    s := s ++ "Admitted into the corpus (do not restate):\n"
    for a in log.admitted do s := s ++ s!"  {a}\n"
  unless log.refuted.isEmpty do
    s := s ++ "Refuted — these are FALSE; avoid conjectures that fail the same way:\n"
    for (a, cex) in log.refuted do s := s ++ s!"  {a}   (counterexample: {cex})\n"
  unless log.merged.isEmpty do
    s := s ++ "Rejected as definitional duplicates of existing statements (avoid trivial restatements):\n"
    for (a, nm) in log.merged do s := s ++ s!"  {a}   (identical to {nm})\n"
  unless log.dups.isEmpty do
    s := s ++ "Rejected as verbatim repeats:\n"
    for a in log.dups do s := s ++ s!"  {a}\n"
  unless log.open.isEmpty do
    s := s ++ "Open — plausibly true but no proof found yet (a different, provable angle may work):\n"
    for a in log.open do s := s ++ s!"  {a}\n"
  unless log.unparseable.isEmpty do
    s := s ++ "Unparseable output lines (follow the format exactly):\n"
    for a in log.unparseable do s := s ++ s!"  {a}\n"
  return s

def renderPrompt (corpus : Corpus) (lastRound : Option BoothLog)
    (perRound : Nat) : MetaM String := do
  let mut facts := ""
  for f in corpus.facts do
    facts := facts ++ s!"  {toString (← ppExpr f.stmt)}\n"
  let feedback := match lastRound with
    | some log => s!"\nResults of your previous round:\n{renderLog log}"
    | none => ""
  return s!"You are the proposer in a verified mathematical discovery system. \
Your proposals are machine-checked: tested on small cases, then proof-searched, \
then admitted by the Lean kernel or rejected. False or duplicate conjectures are \
wasted effort.

Established corpus (Nat = natural numbers, so subtraction is truncated):
{facts}{feedback}
Propose {perRound} NEW conjectures about the operations +, *, -, ^, max, min, \
Nat.gcd on Nat that:
- are universally quantified equations,
- are plausibly TRUE for ALL natural numbers (mind truncated subtraction and 0 cases),
- are not in the corpus and are not trivial restatements of corpus facts,
- ideally connect operations that the corpus does not yet connect.

Output format — exactly one conjecture per line, as a bare Lean 4 term, nothing else:
∀ (a b : Nat), <lhs> = <rhs>
No prose, no numbering, no code fences."

structure BoothConfig where
  rounds : Nat := 3
  perRound : Nat := 8
  knownPrefixes : List Name := [`Nat]
  render : Corpus → Option BoothLog → Nat → MetaM String := renderPrompt

/-- Run booth rounds against `call`, starting from `seed`. Everything the
model proposes goes through the same dedup/refute/hunt/gate pipeline as the
template heuristics. -/
def booth (call : String → IO (Except String String))
    (cfg : BoothConfig := {}) (seed : Corpus := {}) : MetaM Corpus := do
  let known ← collectKnown cfg.knownPrefixes
  let mut corpus := seed
  let mut attempted : Array (Expr × Name) :=
    corpus.facts.map fun f => (f.stmt, f.name)
  let mut lastLog : Option BoothLog := none
  let mut counter := 0
  for round in [1 : cfg.rounds + 1] do
    IO.println ""
    IO.println s!"── booth round {round} ──"
    let prompt ← cfg.render corpus lastLog cfg.perRound
    match ← call prompt with
    | .error e =>
      IO.println s!"  LLM call failed: {e}"
      break
    | .ok text =>
      let mut log : BoothLog := {}
      for cand in extractCandidates text do
        match ← parseConjecture cand with
        | none =>
          log := { log with unparseable := log.unparseable.push cand }
          IO.println s!"  ⊘ {cand} — unparseable, skipped"
        | some stmt =>
          let pretty := toString (← ppExpr stmt)
          if attempted.any (fun p => p.1 == stmt) then
            log := { log with dups := log.dups.push pretty }
            IO.println s!"  ↻ {pretty} — already attempted, skipped"
            continue
          let mut alias? : Option Name := none
          for (a, nm) in attempted do
            if ← defeqSafe a stmt then
              alias? := some nm
              break
          if let some nm := alias? then
            log := { log with merged := log.merged.push (pretty, nm) }
            attempted := attempted.push (stmt, nm)
            IO.println s!"  ≡ {pretty} — definitionally identical to {nm}, merged"
            continue
          counter := counter + 1
          let c : Conjecture :=
            { name := .mkSimple s!"llm_{counter}", stmt, origin := `booth }
          attempted := attempted.push (stmt, c.name)
          let (corpus', outcome) ← judge known corpus c
          corpus := corpus'
          match outcome with
          | .refuted cex =>
            log := { log with refuted := log.refuted.push (pretty, cex) }
            IO.println s!"  ✗ {pretty} — refuted ({cex})"
          | .stillOpen =>
            log := { log with «open» := log.open.push pretty }
            IO.println s!"  ? {pretty} — open"
          | .admitted _ note =>
            log := { log with admitted := log.admitted.push pretty }
            IO.println s!"  ✓ {pretty} — admitted ({note})"
          | .refusedAtGate =>
            IO.println s!"  ! {pretty} — prover evidence REFUSED by the gate"
      lastLog := some log
  return corpus

end Runtime
end Eureka
