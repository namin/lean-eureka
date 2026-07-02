import Lean

/-!
# The discovery gate, running

The model in `Eureka.Gate` realized in Lean metaprogramming: statements are
`Prop`-typed `Expr`s, evidence is a proof term, and the gate is the Lean
kernel (`addDecl`) plus a mechanical audit ladder in front of it.

A `Heuristic` is arbitrary metaprogram code. It can inspect the corpus and
the environment; the type discipline gives it no way to extend the corpus
except through `commitFact` — the LCF move, with `Fact` in the role of `thm`.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- A fact the gate has admitted: a statement with the proof term the kernel
accepted for it. Constructed only by `commitFact`. -/
structure Fact where
  name : Name
  stmt : Expr
  proof : Expr
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
(`commitFact`) remains the authority. -/
def screenFact (p : FactProposal) : MetaM (Option Fact) := do
  if p.stmt.hasSorry || p.proof.hasSorry then return none
  if p.stmt.hasMVar || p.proof.hasMVar then return none
  if p.stmt.hasFVar || p.proof.hasFVar then return none
  unless ← isProp p.stmt do return none
  let ty ← inferType p.proof
  unless ← isDefEq ty p.stmt do return none
  return some { name := p.name, stmt := p.stmt, proof := p.proof }

/-- The gate: screen, submit to the kernel as a theorem, then audit the
axioms the accepted proof depends on. On any refusal the environment is left
unchanged and the proposal is dropped — refusal is safe, exactly as in the
model (`Eureka.admit`'s `else` branch). -/
def commitFact (p : FactProposal) : MetaM (Option Fact) := do
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
