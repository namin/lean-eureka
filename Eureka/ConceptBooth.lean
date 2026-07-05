import Eureka.Concepts

/-!
# The concept booth

Stage two of concept invention (DESIGN_INVENT D6): the LLM as a concept
*proposer*. The model sees the canonical predicate pool and the fate of
its previous round — merged at birth, degenerate, refused, novel — and
proposes definitions in a fixed line format. Each line must survive, in
order: parsing, elaboration at the declared shape's type, the birth gate
(screen, kernel, axiom audit), and the identity probe. The LLM is a
proposer exactly like the template operators — smarter, and no more
trusted. With merge-at-birth cheap, correctness lives entirely in the
gate; the prompt's only job is efficiency (fewer wasted proposals).

The transport is a parameter (`call`), so the pipeline runs
deterministically under test (`InventBoothStub.lean`) and against
Bedrock in `MatroidInventRun.lean`.
-/

open Lean Meta Elab

namespace Eureka
namespace Runtime

/-- A shape the proposer may use: its tag in the line format, the binders
(source text) the body is elaborated under, and the resulting predicate
type. E.g. `⟨"element", "(α : Type) (M : Matroid α) (e : α)", ∀ α, Matroid α → α → Prop⟩`. -/
structure ConceptShape where
  tag : String
  binders : String
  type : Expr

/-- Outcomes of one booth round, fed back into the next round's prompt. -/
structure ConceptBoothLog where
  merged : Array (String × Name) := #[]
  degenerate : Array String := #[]
  novel : Array (String × Nat) := #[]
  refused : Array (String × String) := #[]
  unparseable : Array String := #[]

/-- Parse one proposed line, `name | shape | body`: sanitize the name,
find the shape by tag, elaborate `fun <binders> => (<body> : Prop)` at the
shape's type. Everything about the result is re-checked at the gate; this
is convenience, not trust. -/
def parseConceptCandidate (shapes : Array ConceptShape) (line : String) :
    MetaM (Option ConceptProposal) := do
  -- Under `attempt`: elaboration gets its own heartbeat budget, and a
  -- runtime blowup (or a budget exhausted by earlier rounds' probes) is
  -- an unparseable line, not a crashed run.
  let r ← attempt do
    let parts := (line.splitOn "|").map (·.trimAscii.toString)
    let [rawName, tag, body] := parts
      | return (none : Option ConceptProposal)
    let some sh := shapes.find? (·.tag == tag) | return none
    let chars := rawName.toList.filter fun c => c.isAlphanum || c == '_'
    if chars.isEmpty || !chars.head!.isAlpha then return none
    let src := s!"fun {sh.binders} => ({body} : Prop)"
    match Parser.runParserCategory (← getEnv) `term src with
    | .error _ => return none
    | .ok stx =>
      -- A failed elaboration may *log* errors as well as throw; restore the
      -- message log so a rejected proposal leaves no trace.
      let savedMsgs := (← getThe Core.State).messages
      let result ← try
          let e ← Term.TermElabM.run' <| Term.withoutErrToSorry do
            let e ← Term.elabTerm stx (some sh.type)
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e
          if e.hasSorry || e.hasMVar || e.hasFVar then pure none
          else pure (some e)
        catch _ => pure none
      modifyThe Core.State fun st => { st with messages := savedMsgs }
      let some value := result | return none
      return some { name := .mkSimple (String.mk chars), type := sh.type,
                    value, origin := `conceptBooth }
  return r.join

/-- Keep the lines that look like proposals: strip list markers and code
fences, require the three-column shape. -/
def extractConceptLines (text : String) : List String :=
  text.splitOn "\n"
    |>.map (fun l =>
      ((l.trimAscii.dropWhile fun c =>
        c == '-' || c == '*' || c == '`' || c == '.' || c == ')' || c.isDigit || c == ' ').trimAscii).toString)
    |>.filter (fun l => (l.splitOn "|").length == 3)

def renderConceptLog (log : ConceptBoothLog) : String := Id.run do
  let mut s := ""
  unless log.merged.isEmpty do
    s := s ++ "Merged at birth — known predicates in disguise; the gate certified the \
alias, so these were wasted proposals (do not reinvent existing vocabulary):\n"
    for (a, t) in log.merged do s := s ++ s!"  {a} ≡ {t}\n"
  unless log.degenerate.isEmpty do
    s := s ++ "Degenerate — provably empty or provably universal, certified:\n"
    for a in log.degenerate do s := s ++ s!"  {a}\n"
  unless log.novel.isEmpty do
    s := s ++ "Novel so far — no alias found; these joined the pool (more like these):\n"
    for (a, edges) in log.novel do
      s := s ++ s!"  {a}   ({edges} certified implication edges to known predicates)\n"
  unless log.refused.isEmpty do
    s := s ++ "Refused at the birth gate:\n"
    for (a, r) in log.refused do s := s ++ s!"  {a}   ({r})\n"
  unless log.unparseable.isEmpty do
    s := s ++ "Unparseable output lines (follow the format exactly):\n"
    for a in log.unparseable do s := s ++ s!"  {a}\n"
  return s

/-- A generic prompt: domain blurb, the canonical pool (so the model can
avoid restating it), last round's fates, and the line format. -/
def renderConceptPrompt (domain : String) (shapes : Array ConceptShape)
    (canonical : Array ProbeTarget) (lastRound : Option ConceptBoothLog)
    (perRound : Nat) : MetaM String := do
  let mut canon := ""
  for t in canonical do
    canon := canon ++ s!"  {t.name}\n"
  let mut fmt := ""
  for sh in shapes do
    fmt := fmt ++ s!"<name> | {sh.tag} | <Prop-valued body under binders {sh.binders}>\n"
  let feedback := match lastRound with
    | some log => s!"\nResults of your previous round:\n{renderConceptLog log}"
    | none => ""
  return s!"You are the concept proposer in a verified mathematical discovery system. \
You propose new DEFINITIONS (predicates), not theorems. Every proposal is \
machine-checked at birth: the Lean kernel checks the definition, then an \
identity probe searches for a certified equivalence with existing vocabulary. \
A proposal that is an existing predicate in disguise is merged immediately — \
wasted effort. Provably-empty or provably-universal predicates are discarded \
as degenerate.

Domain: {domain}

Canonical predicates already in the vocabulary (do NOT restate these or \
trivial variants of them):
{canon}{feedback}
Propose {perRound} NEW predicate definitions that:
- are plausibly nonempty and non-universal,
- are not equivalent to any canonical predicate or trivial boolean \
combinations of them,
- name mathematically natural properties worth having facts about.

Output format — exactly one definition per line, nothing else:
{fmt}No prose, no numbering, no code fences."

structure ConceptBoothConfig where
  rounds : Nat := 3
  perRound : Nat := 6
  shapes : Array ConceptShape
  render : Array ProbeTarget → Option ConceptBoothLog → Nat → MetaM String

/-- Run concept-booth rounds against `call`. Everything the model proposes
goes through the same birth gate and identity probes as the template
operators; the per-candidate fates come back as next round's feedback. -/
def conceptBooth (call : String → IO (Except String String))
    (ctx : ProbeCtx) (canonical : Array ProbeTarget)
    (cfg : ConceptBoothConfig) (pool : ConceptPool := {})
    (corpus : Corpus := {}) :
    MetaM (ConceptPool × Corpus × InventStats) := do
  let mut pool := pool
  let mut corpus := corpus
  let mut total : InventStats := {}
  let mut lastLog : Option ConceptBoothLog := none
  for round in [1 : cfg.rounds + 1] do
    IO.println ""
    IO.println s!"── concept booth round {round} ──"
    let prompt ← cfg.render canonical lastLog cfg.perRound
    match ← call prompt with
    | .error e =>
      IO.println s!"  LLM call failed: {e}"
      break
    | .ok text =>
      let mut log : ConceptBoothLog := {}
      let mut proposals : Array ConceptProposal := #[]
      for line in extractConceptLines text do
        match ← parseConceptCandidate cfg.shapes line with
        | none =>
          log := { log with unparseable := log.unparseable.push line }
          IO.println s!"  ⊘ {line} — unparseable, skipped"
        | some p => proposals := proposals.push p
      let (pool', corpus', stats, reports) ←
        inventRoundWith ctx pool corpus canonical proposals
      pool := pool'
      corpus := corpus'
      total := { candidates := total.candidates + stats.candidates
                 refused := total.refused + stats.refused
                 degenerate := total.degenerate + stats.degenerate
                 aliased := total.aliased + stats.aliased
                 novel := total.novel + stats.novel
                 edgeFacts := total.edgeFacts + stats.edgeFacts }
      for r in reports do
        let nm := r.name.getString!
        match r.outcome with
        | .error reason =>
          log := { log with refused := log.refused.push (nm, reason) }
        | .ok (.aliasOf t _ _) =>
          log := { log with merged := log.merged.push (nm, t) }
        | .ok (.degenerate _ _) =>
          log := { log with degenerate := log.degenerate.push nm }
        | .ok (.novel spec genl) =>
          log := { log with novel := log.novel.push (nm, spec.size + genl.size) }
      lastLog := some log
  return (pool, corpus, total)

end Runtime
end Eureka
