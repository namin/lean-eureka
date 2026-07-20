import Lean

/-!
# The discovery gate, running

The intended gate of the `Eureka.Gate` model, instantiated in Lean
metaprogramming: statements are `Prop`-typed `Expr`s, evidence is a proof
term, and the gate is the Lean kernel (`addDecl`) plus a mechanical audit
ladder in front of it. The correspondence to the model is by construction
and inspection — there is no formal refinement proof from this `MetaM`
implementation to the model.

A `Heuristic` is arbitrary metaprogram code. It can inspect the corpus and
the environment; in the provided discovery loops (`fire`, `judge`, the
booth), nothing it returns reaches the corpus except through `commitFact` —
LCF-style in spirit, with `Fact` in the role of `thm`, though the `Fact`
constructor itself is not hidden: the discipline lives in the loops, not in
type abstraction.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- A fact the gate has admitted: a statement with the proof term the kernel
accepted for it. Constructed by `commitFact`; the provided discovery loops
admit facts only through it (the constructor itself is not hidden). -/
structure Fact where
  name : Name
  stmt : Expr
  proof : Expr
  /-- Provenance, carried for materialization and reporting only — the
  gate's checks never consult these fields. -/
  origin : Name := .anonymous
  rung : String := ""
  knownAs : Option Name := none
  deriving Inhabited

/-- The discovery corpus. -/
structure Corpus where
  facts : Array Fact := #[]
  deriving Inhabited

/-- A proposal from an untrusted proposer — a hand-written heuristic, or an
LLM: an alleged fact with alleged evidence. -/
structure FactProposal where
  name : Name
  stmt : Expr
  proof : Expr
  /-- Provenance, passed through to the admitted `Fact` (metadata only). -/
  origin : Name := .anonymous
  rung : String := ""
  knownAs : Option Name := none

/-- A heuristic is arbitrary metaprogram code that proposes facts. -/
structure Heuristic where
  name : Name
  propose : Corpus → MetaM (Array FactProposal)

/-- Axioms an admitted proof may depend on. Anything else — in particular
`sorryAx` and freshly minted axioms — is refused at the gate. -/
def allowedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The cheap front of the gate: reject `sorry`, metavariables, and loose
free variables; require the statement to be a `Prop`; check the alleged proof
against the statement up to definitional equality. The kernel behind
(`commitFact`) remains the authority. A screening check that blows up at
runtime (recursion depth, heartbeats) is a refusal, not an error — refusal
is safe. -/
def screenFact (p : FactProposal) : MetaM (Option Fact) := do
  if p.stmt.hasSorry || p.proof.hasSorry then return none
  if p.stmt.hasMVar || p.proof.hasMVar then return none
  if p.stmt.hasFVar || p.proof.hasFVar then return none
  let ok ← tryCatchRuntimeEx
    (try
      withCurrHeartbeats do
        unless ← isProp p.stmt do return false
        isDefEq (← inferType p.proof) p.stmt
      catch _ => return false)
    (fun _ => return false)
  unless ok do return none
  return some { name := p.name, stmt := p.stmt, proof := p.proof,
                origin := p.origin, rung := p.rung, knownAs := p.knownAs }

/-- The gate: screen, submit to the kernel as a theorem, then audit the
axioms the accepted proof depends on. On any refusal `commitFact`'s own
additions are rolled back and the proposal is dropped — refusal is safe,
exactly as in the model (`Eureka.admit`'s `else` branch). Note the rollback
covers only this function's additions: a heuristic may have added
declarations of its own during `propose`, and those persist — the gate
protects the corpus, not the ambient environment.

The gate runs on its own heartbeat budget (`withCurrHeartbeats`): budgets
are cumulative per command, and whatever untrusted proposers spent hunting
must not starve the admission check itself. -/
def commitFact (p : FactProposal) : MetaM (Option Fact) := withCurrHeartbeats do
  let some f ← screenFact p | return none
  let env ← getEnv
  try
    addDecl <| .thmDecl
      { name := f.name, levelParams := [], type := f.stmt, value := f.proof }
  catch _ =>
    setEnv env
    return none
  let axioms ← collectAxioms f.name
  unless axioms.all allowedAxioms.contains do
    setEnv env
    return none
  return some f

/-- Fire one heuristic: admit what passes the gate, drop (and report) what
does not. The heuristic is untrusted; nothing it returns reaches the corpus
except through `commitFact`. -/
def fire (h : Heuristic) (c : Corpus) :
    MetaM (Corpus × Array Fact × Array FactProposal) := do
  let proposals ← h.propose c
  let mut corpus := c
  let mut admitted := #[]
  let mut rejected := #[]
  for p in proposals do
    match ← commitFact p with
    | some f =>
      corpus := { corpus with facts := corpus.facts.push f }
      admitted := admitted.push f
    | none => rejected := rejected.push p
  return (corpus, admitted, rejected)

end Runtime
end Eureka
