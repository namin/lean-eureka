import EurekaMathlib.MatroidDisco

/-!
# The graph domain (DESIGN_GRAPH)

The generalization arc's per-domain layer — deliberately just three
things, everything else reused as-is: the complement operator (the
involution, `SimpleGraph`'s analog of matroid dualization), the witness
kit for the refuter (small concrete graphs with their simp vocabulary,
the matroid kit's pattern), and agents wrapping the operator. The
generic machinery — extraction, probes, verdicts, the economy,
escalation, `inventedImplAgent` — is imported unchanged; that is the
claim under test.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- Complementation: `P G X ↦ P Gᶜ X` — the involution operator. The
value is built by *elaborating source text*: `Gᶜ`'s `HasCompl` instance
arrives through the Boolean-algebra hierarchy, which the elaborator
resolves where raw `mkAppM` synthesis does not (a generalization
finding — recorded in DESIGN_GRAPH). `@`-application keeps canonical
(implicit-α) and invented (explicit-α) targets uniform. -/
def mkComplementProposal (t : ProbeTarget) (depth : Nat := 1) :
    MetaM (Option ConceptProposal) := do
  let r ← attempt do
    let isSet ← forallTelescope t.type fun xs body => do
      unless body == .sort .zero do throwError "not a predicate"
      unless xs.size == 3 do throwError "wrong shape"
      let xTy ← inferType xs[2]!
      pure (xTy.getAppFn.constName? == some ``Set)
    let binder := if isSet then "(X : Set α)" else "(v : α)"
    let arg := if isSet then "X" else "v"
    let type ← withLocalDeclD `α (mkSort (.succ .zero)) fun α =>
      withLocalDeclD `G (mkApp (mkConst `SimpleGraph [.zero]) α) fun G => do
        let xTy := if isSet then mkApp (mkConst ``Set [.zero]) α else α
        withLocalDeclD `X xTy fun X =>
          mkForallFVars #[α, G, X] (.sort .zero)
    let src := s!"fun (α : Type) (G : SimpleGraph α) {binder} => \
(@{t.name} α Gᶜ {arg} : Prop)"
    match ← elabTermAt type src with
    | .ok value =>
      pure (some { name := .mkSimple s!"compl_{t.name.getString!}",
                   type, value, origin := `complement, depth })
    | .error _ => pure (none : Option ConceptProposal)
  return r.join

/-- Depth-1 complementation over the canonical pool, as an agent. -/
def complementerAgent (canonical : Array ProbeTarget) : Agent where
  name := `complementer
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for t in canonical do
      if let some p ← mkComplementProposal t then
        unless (← getEnv).contains (inventedNs ++ p.name) do
          out := out.push (.concept p)
    return out

/-- Compounding for graphs: complement re-applied to live pool concepts,
depth-capped (DESIGN_INVENT C1–C3, new carrier). -/
def graphCompounderAgent : Agent where
  name := `graph_compounder
  propose := fun _ => return #[]
  proposeP := some fun pool _ => do
    let mut out : Array RProposal := #[]
    for c in pool.live do
      if c.depth < 2 then
        if let some p ← mkComplementProposal c.toTarget (c.depth + 1) then
          unless (← getEnv).contains (inventedNs ++ p.name) do
            out := out.push (.concept p)
    return out

/-! ## The witness kit -/

def gBot : SimpleGraph ℕ := ⊥
def gTop : SimpleGraph ℕ := ⊤
def gsEmpty : Set ℕ := ∅
def gs0 : Set ℕ := {0}
def gs01 : Set ℕ := {0, 1}

/-- The refuter's simp vocabulary: unfold the witnesses, characterize
cliques/independent sets via pairwise over the tiny concrete sets, and
reduce adjacency at `⊥`/`⊤`. -/
def graphRefuterSimpArgs : Array String := #[
  "gBot", "gTop", "gsEmpty", "gs0", "gs01",
  "SimpleGraph.isClique_iff", "SimpleGraph.isIndepSet_iff",
  "Set.pairwise_pair", "Set.pairwise_singleton", "Set.pairwise_empty",
  "SimpleGraph.bot_adj", "SimpleGraph.top_adj",
  "SimpleGraph.isClique_compl", "SimpleGraph.isIndepSet_compl",
  "not_imp"]

def graphInstances : Array (Expr × Expr × String) := #[
  (mkConst ``gBot, mkConst ``gsEmpty, "G := ⊥, X := ∅"),
  (mkConst ``gBot, mkConst ``gs0,    "G := ⊥, X := {0}"),
  (mkConst ``gBot, mkConst ``gs01,   "G := ⊥, X := {0,1}"),
  (mkConst ``gTop, mkConst ``gsEmpty, "G := ⊤, X := ∅"),
  (mkConst ``gTop, mkConst ``gs0,    "G := ⊤, X := {0}"),
  (mkConst ``gTop, mkConst ``gs01,   "G := ⊤, X := {0,1}")]

/-- The assembled graph refuter, invented-aware (`unfold`-prefixed). -/
def graphRefuter : Refuter := fun stmt => do
  let usedInv := (stmt.getUsedConstants.filter
    (inventedNs.isPrefixOf ·)).map toString
  let pre := if usedInv.isEmpty then "" else
    s!"unfold {String.intercalate " " usedInv.toList}; "
  refuteByInstances graphRefuterSimpArgs (mkConst ``Nat)
    graphInstances stmt (pre := pre)

end Runtime
end Eureka
