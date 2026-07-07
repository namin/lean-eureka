import EurekaMathlib.GraphDisco

/-!
# The order domain: Boolean algebras (the third carrier)

The generalization arc, round two — and the first *instance-shaped*
carrier. Matroids and graphs are carrier-shaped (`Matroid α`,
`SimpleGraph α` — a value argument); order-theoretic predicates are
instance-shaped (`IsAtom : ∀ {α} [PartialOrder α] [OrderBot α], α → Prop`),
with *varying* instance signatures across the vocabulary. The port's new
per-domain move is **canonicalization**: extract root predicates whose
instances are derivable from an ambient class (`BooleanAlgebra`), and
declare uniform wrappers `BA.P := fun α [BooleanAlgebra α] a => P a` at
run time (plain `addDecl`, outside the reserved `Invented` namespace, so
the audit boundary is untouched). Everything downstream — probes,
verdicts, merges, the economy, `inventedImplAgent` — sees a uniform
carrier type and runs unchanged.

The involution is `ᶜ`: the order analog of matroid dualization and graph
complement. The expected rhyme: `compl_IsAtom ≡ IsCoatom` grounds at
birth (`isAtom_compl`), depth-2 `compl_compl_P` merges back into
canonical `P` (`compl_compl`).
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- The namespace for canonicalized order predicates. Not under
`Invented` — wrappers are groundings of library vocabulary, not
inventions, and must not trip the reserved-namespace audit. -/
def baNs : Name := `BA

/-- The uniform carrier type: `∀ (α : Type) [BooleanAlgebra α], α → Prop`. -/
def mkBAPredType : MetaM Expr := do
  withLocalDeclD `α (mkSort (.succ .zero)) fun α => do
    let baTy := mkApp (mkConst ``BooleanAlgebra [.zero]) α
    withLocalDecl `inst .instImplicit baTy fun inst => do
      withLocalDeclD `a α fun a =>
        mkForallFVars #[α, inst, a] (.sort .zero)

/-- Element-shaped instance predicates at the root of the environment:
`∀ {α} [i₁] … [iₖ] (a : α), Prop` with every middle binder
instance-implicit. The shape filter only — membership in the domain is
decided by canonicalization below. -/
def rootInstancePredicates : MetaM (Array Name) := do
  let env ← getEnv
  let cands : Array (Name × Expr) :=
    env.constants.fold (init := #[]) fun acc n ci =>
      if n.getPrefix == Name.anonymous && !n.isInternal then
        match ci with
        | .defnInfo t =>
          match t.levelParams with
          | [u] => acc.push (n, t.type.instantiateLevelParams [u] [.zero])
          | _ => acc
        | _ => acc
      else acc
  let mut out := #[]
  for (n, ty) in cands do
    let ok ← attempt <| forallTelescope ty fun xs body => do
      unless body == .sort .zero do return false
      unless xs.size ≥ 3 do return false
      unless (← inferType xs[0]!).isSort do return false
      unless (← inferType xs[xs.size - 1]!) == xs[0]! do return false
      for i in [1 : xs.size - 1] do
        unless (← xs[i]!.fvarId!.getDecl).binderInfo == .instImplicit do
          return false
      return true
    if ok == some true then out := out.push n
  return out.qsort (fun a b => a.toString < b.toString)

/-- Canonicalize a root predicate over the ambient class: declare
`BA.P := fun α [BooleanAlgebra α] a => P a` and return it as a probe
target. `none` when `P`'s instances are not derivable from
`BooleanAlgebra` — the elaboration *is* the domain-membership test. -/
def canonicalizeOrderPredicate (raw : Name) : MetaM (Option ProbeTarget) := do
  let type ← mkBAPredType
  let name := baNs ++ raw
  if (← getEnv).contains name then
    return some { name, type }
  let src := s!"fun (α : Type) [BooleanAlgebra α] (a : α) => ({raw} a : Prop)"
  match ← elabTermAt type src with
  | .error _ => return none
  | .ok value =>
    let r ← attempt <| addDecl <| .defnDecl
      { name, levelParams := [], type, value, hints := .abbrev, safety := .safe }
    if r.isSome then return some { name, type } else return none

/-- Complementation over the ambient Boolean algebra: `P a ↦ P aᶜ` — the
involution operator. Value built by elaborating source text (the graph
arc's finding); `@`-application keeps canonical wrappers and invented
concepts uniform, both inhabiting the uniform carrier type. -/
def mkOrderComplProposal (t : ProbeTarget) (depth : Nat := 1) :
    MetaM (Option ConceptProposal) := do
  let r ← attempt do
    let type ← mkBAPredType
    unless ← defeqSafe t.type type do throwError "wrong shape"
    let src := s!"fun (α : Type) [inst : BooleanAlgebra α] (a : α) => \
(@{t.name} α inst aᶜ : Prop)"
    match ← elabTermAt type src with
    | .ok value =>
      pure (some { name := .mkSimple s!"compl_{t.name.getString!}",
                   type, value, origin := `order_compl, depth })
    | .error _ => pure (none : Option ConceptProposal)
  return r.join

/-- Depth-1 complementation over the canonical pool, as an agent. -/
def orderComplementerAgent (canonical : Array ProbeTarget) : Agent where
  name := `order_complementer
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for t in canonical do
      if let some p ← mkOrderComplProposal t then
        unless (← getEnv).contains (inventedNs ++ p.name) do
          out := out.push (.concept p)
    return out

/-- Compounding for orders: complement re-applied to live pool concepts,
depth-capped (DESIGN_INVENT C1–C3, third carrier). -/
def orderCompounderAgent : Agent where
  name := `order_compounder
  propose := fun _ => return #[]
  proposeP := some fun pool _ => do
    let mut out : Array RProposal := #[]
    for c in pool.live do
      if c.depth < 2 then
        if let some p ← mkOrderComplProposal c.toTarget (c.depth + 1) then
          unless (← getEnv).contains (inventedNs ++ p.name) do
            out := out.push (.concept p)
    return out

/-- The grounding pool for a domain whose lemmas live at the root:
theorems *mentioning* any of the raw predicates. `collectKnown` is
namespace-prefix based, and order vocabulary is scattered —
`isAtom_compl` lives at the root, not under `IsAtom`. -/
def collectKnownMentioning (heads : Array Name) : MetaM (Array KnownLemma) := do
  let env ← getEnv
  let cands : Array (Name × Expr × List Level) :=
    env.constants.fold (init := #[]) fun acc n ci =>
      match ci with
      | .thmInfo t =>
        if t.type.getUsedConstants.any heads.contains then
          match t.levelParams with
          | [] => acc.push (n, t.type, [])
          | [u] =>
            acc.push (n, t.type.instantiateLevelParams [u] [Level.zero],
                      [Level.zero])
          | _ => acc
        else acc
      | _ => acc
  let mut out := #[]
  for (n, ty, levels) in cands do
    if let some (binders, rel, head, head2) ← statementKey ty then
      out := out.push { name := n, type := ty, levels, binders, rel, head, head2 }
  return out

/-! ## The witness kit

Two concrete Boolean algebras: `Bool` (two elements — degenerate on
purpose: `true` is atom, coatom, and top at once) and `Bool × Bool`
(four elements — separates atoms from ⊤, the shape `Bool` cannot).
Both instances are computable, so `decide` is the kit's first rung;
the simp vocabulary is the fallback. -/

def bFF : Bool × Bool := (false, false)
def bFT : Bool × Bool := (false, true)
def bTF : Bool × Bool := (true, false)
def bTT : Bool × Bool := (true, true)

/-- The refuter's simp vocabulary: unfold the raw predicates (plain defs
— equation lemmas exist) and the kit's named elements, and characterize
the order at the witnesses. -/
def orderRefuterSimpArgs : Array String := #[
  "bFF", "bFT", "bTF", "bTT",
  "IsAtom", "IsCoatom", "IsMin", "IsMax", "IsTop", "IsBot",
  "SupIrred", "SupPrime", "InfIrred", "InfPrime",
  "Prod.le_def", "Prod.lt_iff", "Prod.ext_iff",
  "lt_iff_le_not_ge",
  "isAtom_compl", "isCoatom_compl", "compl_compl",
  "not_forall", "_root_.not_imp"]

def orderBoolInstances : Array (Expr × Expr × String) := #[
  (mkConst ``Bool.instBooleanAlgebra, mkConst ``Bool.false, "α := Bool, a := false"),
  (mkConst ``Bool.instBooleanAlgebra, mkConst ``Bool.true,  "α := Bool, a := true")]

def orderBool2Instances : Array (Expr × Expr × String) :=
  let inst := mkApp4 (mkConst ``Prod.instBooleanAlgebra [.zero, .zero])
    (mkConst ``Bool) (mkConst ``Bool)
    (mkConst ``Bool.instBooleanAlgebra) (mkConst ``Bool.instBooleanAlgebra)
  #[(inst, mkConst ``bFF, "α := Bool², a := (f,f)"),
    (inst, mkConst ``bFT, "α := Bool², a := (f,t)"),
    (inst, mkConst ``bTF, "α := Bool², a := (t,f)"),
    (inst, mkConst ``bTT, "α := Bool², a := (t,t)")]

/-- The unfold prefix for the order refuter: the invented transitive
closure *plus* every `BA.*` wrapper reachable from the statement or from
an invented body. Wrappers are raw `addDecl` definitions — simp cannot
unfold them by name (no equation lemmas), only `unfold`/delta; the same
disease `inventedUnfoldNames` treats, one namespace over. -/
def orderUnfoldPre (stmt : Expr) : MetaM String := do
  let inv ← inventedUnfoldNames stmt
  let mut ba : Array Name := stmt.getUsedConstants.filter (baNs.isPrefixOf ·)
  for n in inv do
    if let some ci := (← getEnv).find? n then
      if let some v := ci.value? then
        for m in v.getUsedConstants do
          if baNs.isPrefixOf m && !ba.contains m then
            ba := ba.push m
  let all := inv ++ ba
  if all.isEmpty then return ""
  return s!"unfold {String.intercalate " " (all.toList.map toString)}; "

/-- The assembled order refuter: `decide` first (both witnesses are
computable, and the kernel reduces through the unfolded goals), the simp
vocabulary as fallback; invented- and wrapper-aware either way. -/
def orderRefuter : Refuter := fun stmt => do
  let pre := (← orderUnfoldPre stmt) ++ "first | decide | "
  let bool2Ty := mkApp2 (mkConst ``Prod [.zero, .zero])
    (mkConst ``Bool) (mkConst ``Bool)
  if let some r ← refuteByInstances orderRefuterSimpArgs (mkConst ``Bool)
      orderBoolInstances stmt (pre := pre) then
    return some r
  refuteByInstances orderRefuterSimpArgs bool2Ty
    orderBool2Instances stmt (pre := pre)

end Runtime
end Eureka
