import EurekaMathlib.Domain

/-!
# Matroid discovery proper

Template agents over the predicates extracted from the `Matroid` namespace
— nothing matroid-specific is hardcoded except the templates' shapes:

* `implicationsAgent` — `P X → Q X` for same-shape pairs;
* `exclusionsAgent`  — `P X → ¬ Q X`;
* `dualityAgent`     — `P M✶ X ↔ Q M X` (the Whitney-duality family: the
  conjecture shape the formal-disco baseline run could state but not prove);
* `singletonAgent`   — `P e ↔ Q {e}` bridging element and set predicates.

Run through the population engine (worth, budget, kill rule) with the
`Matroid` grounding pool, then LLM booth rounds on top. There is no
counterexample search in this domain: false conjectures land in `open`,
and the honest reading of `open` is "unrefuted and unproved".
-/

open Lean Meta

namespace Eureka
namespace Runtime

private def mkSingleton (α e : Expr) : MetaM Expr :=
  mkAppOptM ``Singleton.singleton
    #[some α, some (mkApp (mkConst ``Set [Level.zero]) α), none, some e]

/-- `∀ α M X, P M X → ¬ Q M X` for same-shape pairs. -/
def exclusionsAgent (carrier : Name) (preds : Array PredInfo) : Agent where
  name := `exclusions
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for P in preds do
      for Q in preds do
        if P.name != Q.name && P.shape == Q.shape then
          let stmt ← mkPredForall carrier P.shape fun M X => do
            mkArrow (← mkAppM P.name #[M, X]) (mkNot (← mkAppM Q.name #[M, X]))
          out := out.push (.fact
            { name := .mkSimple s!"{P.name.getString!}_excl_{Q.name.getString!}",
              stmt, origin := `exclusions })
    return out

/-- `∀ α M X, P M X → Q M X` for same-shape pairs, as an agent. -/
def implicationsAgent (carrier : Name) (preds : Array PredInfo) : Agent where
  name := `implications
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for P in preds do
      for Q in preds do
        if P.name != Q.name && P.shape == Q.shape then
          out := out.push (.fact (← mkImplConjecture carrier P Q))
    return out

/-- `∀ α M X, P M✶ X ↔ Q M X` over same-shape pairs (`P = Q` allowed:
self-duality is a real question). -/
def dualityAgent (preds : Array PredInfo) : Agent where
  name := `duality
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for P in preds do
      for Q in preds do
        if P.shape == Q.shape then
          let stmt ← mkPredForall `Matroid P.shape fun M X => do
            let dualM ← mkAppM ``Matroid.dual #[M]
            return mkApp2 (mkConst ``Iff)
              (← mkAppM P.name #[dualM, X]) (← mkAppM Q.name #[M, X])
          out := out.push (.fact
            { name := .mkSimple s!"dual_{P.name.getString!}_{Q.name.getString!}",
              stmt, origin := `duality })
    return out

/-- `∀ α M e, P M e ↔ Q M {e}` for element predicate `P`, set predicate `Q`. -/
def singletonAgent (preds : Array PredInfo) : Agent where
  name := `singleton
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for P in preds do
      for Q in preds do
        if P.shape == PredShape.element && Q.shape == PredShape.set then
          let stmt ← withLocalDeclD `α (mkSort (.succ .zero)) fun α => do
            let carrierTy := mkApp (mkConst `Matroid [Level.zero]) α
            withLocalDeclD `M carrierTy fun M =>
              withLocalDeclD `e α fun e => do
                let sing ← mkSingleton α e
                mkForallFVars #[α, M, e] <| mkApp2 (mkConst ``Iff)
                  (← mkAppM P.name #[M, e]) (← mkAppM Q.name #[M, sing])
          out := out.push (.fact
            { name := .mkSimple s!"sing_{P.name.getString!}_{Q.name.getString!}",
              stmt, origin := `singleton })
    return out

/-!
## Matroid-shaped generative operators (DESIGN_INVENT D5)

Dualization and singleton-lift are domain-shaped; they live here. The
generic operators (conjunction, negated-conjunct) are in
`Eureka.Concepts`.
-/

/-- Dualization: `P M X ↦ P M✶ X`, either shape. `depth` is the
product's generative depth (C2): 1 over canonical inputs; compounding an
invented input passes `input.depth + 1`. -/
def mkDualizeProposal (t : ProbeTarget) (depth : Nat := 1) :
    MetaM (Option ConceptProposal) := do
  let r ← attempt <| forallTelescope t.type fun xs body => do
    unless body == .sort .zero do return none
    unless xs.size == 3 do return none
    let dualM ← mkAppM ``Matroid.dual #[xs[1]!]
    let app := mkAppN (mkConst t.name t.levels) #[xs[0]!, dualM, xs[2]!]
    let value ← mkLambdaFVars xs app
    let type ← mkForallFVars xs (.sort .zero)
    return some { name := .mkSimple s!"dual_{t.name.getString!}",
                  type, value, origin := `dualize, depth }
  return r.join

/-- Singleton-lift: a set predicate becomes an element predicate,
`P M X ↦ fun M e => P M {e}` — the element↔set bridge as an operator. -/
def mkSingletonLiftProposal (t : ProbeTarget) (depth : Nat := 1) :
    MetaM (Option ConceptProposal) := do
  let r ← attempt <| forallTelescope t.type fun xs body => do
    unless body == .sort .zero do return none
    unless xs.size == 3 do return none
    let α := xs[0]!
    let xTy ← inferType xs[2]!
    unless xTy.getAppFn.constName? == some ``Set do return none
    withLocalDeclD `e α fun e => do
      let sing ← mkSingleton α e
      let app := mkAppN (mkConst t.name t.levels) #[α, xs[1]!, sing]
      let value ← mkLambdaFVars #[α, xs[1]!, e] app
      let type ← mkForallFVars #[α, xs[1]!, e] (.sort .zero)
      return some { name := .mkSimple s!"elem_{t.name.getString!}",
                    type, value, origin := `singletonLift, depth }
  return r.join

/-- Compounding (slice two, C1–C3): dualize and singleton-lift over the
*live pool*, inputs below the depth cap, products not already born. The
boolean operators do not re-enter. -/
def compoundProposals (pool : ConceptPool) (depthCap : Nat := 2) :
    MetaM (Array ConceptProposal) := do
  let ops : List (ProbeTarget → Nat → MetaM (Option ConceptProposal)) :=
    [fun t d => mkDualizeProposal t d, fun t d => mkSingletonLiftProposal t d]
  let mut out : Array ConceptProposal := #[]
  for c in pool.live do
    if c.depth < depthCap then
      for mk in ops do
        if let some p ← mk c.toTarget (c.depth + 1) then
          unless (← getEnv).contains (inventedNs ++ p.name) do
            out := out.push p
  return out

/-- The compounding operator agent (slice two): reads the pool via
`proposeP`. -/
def compounderAgent : Agent where
  name := `compounder
  propose := fun _ => return #[]
  proposeP := some fun pool _ => do
    return (← compoundProposals pool).map .concept

/-- Depth-1 dualization over the canonical pool, as an agent. -/
def dualizerAgent (canonical : Array ProbeTarget) : Agent where
  name := `dualizer
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for t in canonical do
      if let some p ← mkDualizeProposal t then
        unless (← getEnv).contains (inventedNs ++ p.name) do
          out := out.push (.concept p)
    return out

/-- Proposes implications between live invented concepts and the
canonical pool, both directions — the agent that makes invention *pay*:
its admissions route through the concept-aware judge and credit the
concepts' inventors. Rotates its enumeration by corpus size so the
per-agent cap sees fresh pairs each generation. -/
def inventedImplAgent (canonical : Array ProbeTarget) : Agent where
  name := `invented_impls
  propose := fun _ => return #[]
  proposeP := some fun pool corpus => do
    let mut pairs : Array (ProbeTarget × ProbeTarget) := #[]
    for c in pool.live do
      for t in canonical do
        if ← targetsCompatible c.toTarget t then
          pairs := pairs.push (c.toTarget, t)
          pairs := pairs.push (t, c.toTarget)
    if pairs.isEmpty then return #[]
    let offset := (corpus.facts.size * 7) % pairs.size
    let rotated := pairs.extract offset pairs.size ++ pairs.extract 0 offset
    let mut out : Array RProposal := #[]
    for (a, b) in rotated do
      if let some stmt ← mkImplStmt a b then
        out := out.push (.fact
          { name := .mkSimple s!"{a.name.getString!}_imp_{b.name.getString!}",
            stmt, origin := `invented_impls })
    return out

/-- Conjunction over canonical pairs, as an agent — the derby's noise
arm; does not compound (C1). -/
def conjAgent (canonical : Array ProbeTarget) : Agent where
  name := `conj
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for i in [0 : canonical.size] do
      for j in [i + 1 : canonical.size] do
        if let some p ← mkConjProposal false canonical[i]! canonical[j]! then
          unless (← getEnv).contains (inventedNs ++ p.name) do
            out := out.push (.concept p)
    return out

/-!
## The refuter kit

Concrete witnesses for `refuteByInstances`, as named definitions so the
refuter's simp call can unfold them by name (call sites `open
Eureka.Runtime`, which is how the unqualified names in the simp vocabulary
resolve). The pool is small and pointed: `uniqueBaseOn {0} {0,1}` has a
coloop and a loop in one matroid. Call sites should
`set_option linter.unusedSimpArgs false` — the vocabulary is a union over
all instances, so per-goal unused entries are by design.
-/

def mFree : Matroid ℕ := Matroid.freeOn {0}
def mLoopy : Matroid ℕ := Matroid.loopyOn {0}
def mUB : Matroid ℕ := Matroid.uniqueBaseOn {0} {0, 1}
def mEmpty : Matroid ℕ := Matroid.emptyOn ℕ
def sEmpty : Set ℕ := ∅
def s0 : Set ℕ := {0}
def s1 : Set ℕ := {1}
def s01 : Set ℕ := {0, 1}

/-- `uniqueBaseOn`'s base characterization is conditional on `I ⊆ E`;
discharge it once, at our instance, so simp can use it unconditionally. -/
theorem ubOn_isBase_iff {B : Set ℕ} :
    (Matroid.uniqueBaseOn ({0} : Set ℕ) {0, 1}).IsBase B ↔ B = {0} :=
  Matroid.uniqueBaseOn_isBase_iff (by simp)

/-- The refuter's simp vocabulary: unfold the witnesses, characterize the
predicates at the concrete constructions, reduce duality and singletons. -/
def matroidRefuterSimpArgs : Array String := #[
  "mFree", "mLoopy", "mUB", "mEmpty", "sEmpty", "s0", "s1", "s01",
  "ubOn_isBase_iff",
  "Matroid.dep_iff", "Matroid.coindep_def", "Matroid.isCocircuit_def",
  "Matroid.loopyOn_isLoop_iff", "Matroid.uniqueBaseOn_isLoop_iff",
  "← Matroid.singleton_dep",
  "Matroid.isColoop_iff_forall_mem_isBase",
  "Matroid.empty_not_isCircuit", "Matroid.singleton_isCircuit",
  "not_imp"]

/-- The witness pool: set-shaped and element-shaped instances; shape
mismatches fail `refuteByInstances`' type check and are skipped. -/
def matroidInstances : Array (Expr × Expr × String) := #[
  (mkConst ``mFree,  mkConst ``sEmpty, "M := freeOn {0}, X := ∅"),
  (mkConst ``mFree,  mkConst ``s0,     "M := freeOn {0}, X := {0}"),
  (mkConst ``mLoopy, mkConst ``sEmpty, "M := loopyOn {0}, X := ∅"),
  (mkConst ``mLoopy, mkConst ``s0,     "M := loopyOn {0}, X := {0}"),
  (mkConst ``mUB,    mkConst ``sEmpty, "M := uniqueBaseOn {0} {0,1}, X := ∅"),
  (mkConst ``mUB,    mkConst ``s0,     "M := uniqueBaseOn {0} {0,1}, X := {0}"),
  (mkConst ``mUB,    mkConst ``s1,     "M := uniqueBaseOn {0} {0,1}, X := {1}"),
  (mkConst ``mUB,    mkConst ``s01,    "M := uniqueBaseOn {0} {0,1}, X := {0,1}"),
  (mkConst ``mFree,  mkNatLit 0,       "M := freeOn {0}, e := 0"),
  (mkConst ``mLoopy, mkNatLit 0,       "M := loopyOn {0}, e := 0"),
  (mkConst ``mUB,    mkNatLit 0,       "M := uniqueBaseOn {0} {0,1}, e := 0"),
  (mkConst ``mUB,    mkNatLit 1,       "M := uniqueBaseOn {0} {0,1}, e := 1"),
  (mkConst ``mEmpty, mkNatLit 0,       "M := emptyOn ℕ, e := 0")]

/-- The assembled matroid refuter, ready for `judge` / `EvolveConfig`. -/
def matroidRefuter : Refuter :=
  refuteByInstances matroidRefuterSimpArgs (mkConst ``Nat) matroidInstances

/-- Booth prompt for the matroid domain. -/
def renderMatroidPrompt (preds : Array PredInfo)
    (corpus : Corpus) (lastRound : Option BoothLog) (perRound : Nat) :
    MetaM String := do
  let mut facts := ""
  for f in corpus.facts do
    facts := facts ++ s!"  {toString (← ppExpr f.stmt)}\n"
  let predList := String.intercalate ", " (preds.toList.map (·.name.toString))
  let feedback := match lastRound with
    | some log => s!"\nResults of your previous round:\n{renderLog log}"
    | none => ""
  return s!"You are the proposer in a verified discovery system exploring matroid \
theory in Lean 4 with Mathlib.

Established corpus:
{facts}{feedback}
Available predicates: {predList} (also `Matroid.dual` — `M✶` — and set
operations on `Set α`).

Propose {perRound} NEW conjectures about matroids that:
- are plausibly TRUE for all matroids (they are proof-searched and \
kernel-checked; there is no counterexample search, so false conjectures \
waste proof effort and land as 'open'),
- are not in the corpus and not trivial restatements,
- connect predicates the corpus does not yet connect (duality, complements, \
unions, the ground set M.E).

Output format — one conjecture per line, a bare Lean 4 term, nothing else:
∀ (α : Type) (M : Matroid α) (X : Set α), <statement>
or with (e : α) for element statements. Use full names (Matroid.Indep, \
M.IsBase, M✶, Set α). No prose, no numbering, no code fences."

end Runtime
end Eureka
