import Eureka.Booth

/-!
# The proposal booth, stage two: heuristics as code

The runtime analogue of the model's `.rule` proposals: the LLM writes a
*heuristic* — a Lean term of type `Corpus → MetaM (Array Conjecture)` — and
the system elaborates it, checks it against the rule policy, compiles it,
installs it, and fires it. Everything the born heuristic proposes still goes
through the fact gate; per `Eureka.discovery_sound`, corpus soundness never
depended on the rule gate, and per `Eureka.ruleGated_heuristics_invariant`,
what the rule policy buys is an invariant over the heuristic population.

The rule policy here is mechanical: the term elaborates at the interface
type with no `sorry`/metavariables/free variables, and references no
constant on the effect denylist (`IO.Process`, `IO.FS`, the LLM client).
The denylist is shallow (it inspects the term's own constants); OS-level
sandboxing of metaprograms is out of scope, exactly as in lean-sage's booth
— the theorems protect the corpus, not the filesystem. A non-terminating
heuristic would hang the loop; a watchdog is future work.
-/

open Lean Meta Elab

namespace Eureka
namespace Runtime

/-- The interface type a proposed heuristic must inhabit. -/
abbrev ProposeFn := Corpus → MetaM (Array Conjecture)

def proposeFnType : MetaM Expr :=
  mkArrow (mkConst ``Corpus)
    (mkApp (mkConst ``MetaM) (mkApp (mkConst ``Array [levelZero]) (mkConst ``Conjecture)))

private unsafe def evalProposeFnUnsafe (e : Expr) : MetaM ProposeFn := do
  Meta.evalExpr ProposeFn (← proposeFnType) e

/-- Compile an elaborated, policy-checked heuristic term into a runnable
function (via the interpreter). -/
@[implemented_by evalProposeFnUnsafe]
opaque evalProposeFn (e : Expr) : MetaM ProposeFn

/-- The effect denylist: constants a proposed heuristic may not reference.
Shallow by design — see the module docstring. -/
def bannedPrefixes : List Name := [`IO.Process, `IO.FS, `Eureka.LLM]

/-- The rule policy `P` (the model's `admitRuleGated`): `none` = clean,
`some msg` = violation. -/
def rulePolicy (e : Expr) : Option String := Id.run do
  for c in e.getUsedConstants do
    for p in bannedPrefixes do
      if p.isPrefixOf c then
        return some s!"references banned constant {c}"
  return none

/-- Elaborate a proposed term at the given type, with names from `Lean`,
`Lean.Meta`, and `Eureka.Runtime` opened. Returns the elaborated term or the
error text (for LLM feedback). -/
def elabTermAt (type : Expr) (src : String) : MetaM (Except String Expr) := do
  let src := s!"open Lean Meta Eureka.Runtime in\n{src}"
  match Parser.runParserCategory (← getEnv) `term src with
  | .error e => return .error s!"parse error: {e}"
  | .ok stx =>
    let savedMsgs := (← getThe Core.State).messages
    let result ← try
        let e ← Term.TermElabM.run' <| Term.withoutErrToSorry do
          let e ← Term.elabTerm stx (some type)
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
        if e.hasSorry then pure (.error "elaborated term contains sorry")
        else if e.hasMVar then pure (.error "elaborated term contains metavariables")
        else if e.hasFVar then pure (.error "elaborated term contains free variables")
        else pure (.ok e)
      catch ex =>
        pure (.error (← ex.toMessageData.toString))
    modifyThe Core.State fun st => { st with messages := savedMsgs }
    return result

/-- Elaborate a proposed heuristic term at the stage-one interface type. -/
def elabProposeTerm (src : String) : MetaM (Except String Expr) := do
  elabTermAt (← proposeFnType) src

/-- The rule gate: elaborate, policy-check, compile. On success the born
heuristic is returned, ready to fire. -/
def installHeuristic (name : Name) (src : String) :
    MetaM (Except String ConjHeuristic) := do
  match ← elabProposeTerm src with
  | .error e => return .error e
  | .ok e =>
    if let some violation := rulePolicy e then
      return .error s!"rule policy violation: {violation}"
    let fn ← evalProposeFn e
    return .ok { name, propose := fn }

/-- Extract the proposed term: the content of the first code fence, else the
whole response. -/
def extractTerm (text : String) : String := Id.run do
  let parts := text.splitOn "```"
  if parts.length ≥ 3 then
    let body := parts[1]!
    let body := if body.startsWith "lean" then body.drop 4 else body
    return body.trimAscii.toString
  return text.trimAscii.toString

/-- Fire a born heuristic: its conjectures pass through dedup and the same
judge as every other proposal. Returns the grown corpus and a rendering of
the outcomes (for LLM feedback). -/
def fireRule (known : Array KnownLemma) (corpus : Corpus)
    (h : ConjHeuristic) (attempted : Array (Expr × Name)) :
    MetaM (Corpus × Array (Expr × Name) × String) := do
  let mut corpus := corpus
  let mut attempted := attempted
  let mut report := ""
  let some conjectures ← attempt (h.propose corpus)
    | return (corpus, attempted, "the heuristic crashed when fired")
  if conjectures.isEmpty then
    return (corpus, attempted, "the heuristic proposed nothing")
  let mut counter := 0
  for c in conjectures do
    let pretty := toString (← ppExpr c.stmt)
    if attempted.any (fun p => p.1 == c.stmt) then
      IO.println s!"    ↻ {pretty} — already attempted, skipped"
      report := report ++ s!"repeat: {pretty}\n"
      continue
    let mut alias? : Option Name := none
    for (a, nm) in attempted do
      if ← defeqSafe a c.stmt then
        alias? := some nm
        break
    if let some nm := alias? then
      attempted := attempted.push (c.stmt, nm)
      IO.println s!"    ≡ {pretty} — definitionally identical to {nm}, merged"
      report := report ++ s!"duplicate of {nm}: {pretty}\n"
      continue
    counter := counter + 1
    let conj : Conjecture :=
      { name := .mkSimple s!"{h.name}_{counter}", stmt := c.stmt, origin := h.name }
    attempted := attempted.push (c.stmt, conj.name)
    let (corpus', outcome) ← judge known corpus conj
    corpus := corpus'
    match outcome with
    | .refuted cex =>
      IO.println s!"    ✗ {pretty} — refuted ({cex})"
      report := report ++ s!"refuted ({cex}): {pretty}\n"
    | .stillOpen =>
      IO.println s!"    ? {pretty} — open"
      report := report ++ s!"open (no proof found): {pretty}\n"
    | .admitted _ note =>
      IO.println s!"    ✓ {pretty} — admitted ({note})"
      report := report ++ s!"admitted ({note}): {pretty}\n"
    | .refusedAtGate =>
      IO.println s!"    ! {pretty} — evidence REFUSED by the gate"
      report := report ++ s!"refused by gate: {pretty}\n"
  return (corpus, attempted, report)

/-- Example heuristic source shown to the LLM (this is `commH`'s body,
specialized): a worked example of the Expr-building idiom. -/
def exampleSource : String :=
"fun _corpus => do
  let natTy := mkConst ``Nat
  let mut out := #[]
  for op in opPool do
    let stmt ← withLocalDeclD `a natTy fun a =>
      withLocalDeclD `b natTy fun b => do
        mkForallFVars #[a, b] (← mkEq (← mkOp op a b) (← mkOp op b a))
    out := out.push { name := Name.mkSimple s!\"{op.tag}_comm\", stmt, origin := `example }
  return out"

def renderRulePrompt (corpus : Corpus) (feedback : Option String) :
    MetaM String := do
  let mut facts := ""
  for f in corpus.facts do
    facts := facts ++ s!"  {toString (← ppExpr f.stmt)}\n"
  let fb := match feedback with
    | some s => s!"\nFeedback on your previous proposal:\n{s}\n"
    | none => ""
  return s!"You are writing a discovery HEURISTIC (not conjectures directly) for a \
verified discovery system running inside Lean 4.

The system's corpus of established facts about Nat operations:
{facts}{fb}
Write ONE Lean 4 term of type `Corpus → MetaM (Array Conjecture)`. It runs as \
a metaprogram: it may inspect the corpus and must BUILD conjecture statements \
as `Expr`s. Relevant API (your code is elaborated with `open Lean Meta \
Eureka.Runtime in` prefixed):
- `structure Conjecture where name : Name; stmt : Expr; origin : Name`
- `structure Corpus where facts : Array Fact` and `Fact` has `name : Name, stmt : Expr`
- `opPool : List Op` (add, mul, sub, pow, max, min, gcd) and `mkOp : Op → Expr → Expr → MetaM Expr`; `Op` has `tag : String`
- `withLocalDeclD`, `mkForallFVars`, `mkEq`, `mkAppM`, `mkNatLit`, `mkConst`

Example heuristic:
```lean
{exampleSource}
```

Your heuristic should generate a FAMILY of conjectures the corpus does not \
cover yet (e.g. a law schema over operation pairs, or conjectures derived by \
inspecting corpus facts). Each conjecture is machine-tested and kernel-checked; \
false ones are refuted and wasted. Policy forbids IO and process access.

Output exactly one Lean term in a single ```lean code block. No imports, no \
`def`, no commentary outside the block."

structure RuleBoothConfig where
  rounds : Nat := 2
  retries : Nat := 2

/-- Booth stage two: each round asks the LLM for a heuristic, installs it
through the rule gate (with error-feedback retries), fires it, and feeds the
outcomes back into the next round. -/
def boothRules (call : String → IO (Except String String))
    (cfg : RuleBoothConfig := {}) (seed : Corpus := {}) : MetaM Corpus := do
  let known ← collectKnown [`Nat]
  let mut corpus := seed
  let mut attempted : Array (Expr × Name) :=
    corpus.facts.map fun f => (f.stmt, f.name)
  let mut feedback : Option String := none
  let mut counter := 0
  for round in [1 : cfg.rounds + 1] do
    IO.println ""
    IO.println s!"── rule round {round} ──"
    let mut installed : Option ConjHeuristic := none
    let mut tries := 0
    while installed.isNone && tries ≤ cfg.retries do
      tries := tries + 1
      let prompt ← renderRulePrompt corpus feedback
      match ← call prompt with
      | .error e =>
        IO.println s!"  LLM call failed: {e}"
        return corpus
      | .ok text =>
        counter := counter + 1
        let src := extractTerm text
        match ← installHeuristic (.mkSimple s!"llmrule_{counter}") src with
        | .error e =>
          IO.println s!"  ✗ proposal rejected by the rule gate: {e}"
          feedback := some s!"Your heuristic was REJECTED: {e}\nFix it and try again."
        | .ok h =>
          IO.println s!"  ✓ heuristic {h.name} admitted by the rule gate; firing:"
          installed := some h
    match installed with
    | none =>
      IO.println s!"  no admissible heuristic after {tries} tries; moving on"
      feedback := none
    | some h =>
      let (corpus', attempted', report) ← fireRule known corpus h attempted
      corpus := corpus'
      attempted := attempted'
      -- A shotgun heuristic can produce hundreds of outcome lines; feed a
      -- sample back, not the flood.
      let lines := report.splitOn "\n"
      let sample := String.intercalate "\n" (lines.take 15)
      let elided := if lines.length > 15 then s!"\n… ({lines.length - 15} more)" else ""
      feedback := some s!"Your previous heuristic {h.name} fired with these results:\n\
{sample}{elided}\nPropose a DIFFERENT heuristic exploring what is still uncovered. \
Favor precision over volume: refuted conjectures are wasted effort."
  return corpus

end Runtime
end Eureka
