import EurekaMathlib

/-!
Acceptance test 1 (DESIGN_INVENT): **the tower's own examples, at birth.**

The formal-disco matroid runs invented a synonym tower — three variants of
"loop", four of "cocircuit" (REPORT_ALIGN) — detected only post-hoc, at
~75s per alignment probe. Here the literal baseline inventions are fed to
the birth gate as candidate concepts, and every one must merge *at birth*
with a kernel-checked certificate naming its canonical Mathlib target:
the baseline's entire Phase 1+2 alignment result, reproduced in-process,
before the duplicates ever join the pool.

Also exercises the domain-shaped D5 operator: dualization. The dual of
`Matroid.IsCircuit` is proposed as a new concept and merges into
`Matroid.IsCocircuit` — the operator's product was already canonical, and
the gate knows it immediately.

Run with `lake env lean MatroidInventStub.lean` (not in CI: needs the
Mathlib build).
-/

open Lean Meta Eureka.Runtime

/-! The literal tower, bodies per the baseline's alignment tables. -/

def cand_loop_element {α : Type} (M : Matroid α) (e : α) : Prop :=
  e ∈ M.E ∧ ¬ M.Indep {e}

def cand_is_loop_specialized {α : Type} (M : Matroid α) (e : α) : Prop :=
  e ∈ M.E ∧ ¬ M.Indep {e}

def cand_loop_as_dual_coloop {α : Type} (M : Matroid α) (e : α) : Prop :=
  M✶.IsColoop e

def cand_cocircuit_as_dual_circuit {α : Type} (M : Matroid α) (X : Set α) : Prop :=
  M✶.IsCircuit X

def cand_is_cocircuit_def {α : Type} (M : Matroid α) (X : Set α) : Prop :=
  M✶.IsCircuit X

def cand_dep_invented {α : Type} (M : Matroid α) (X : Set α) : Prop :=
  X ⊆ M.E ∧ ¬ M.Indep X

def proposalFromDef (base : Name) (defn : Name) : MetaM ConceptProposal := do
  let ci ← getConstInfo defn
  return { name := base, type := ci.type, value := ci.value!, origin := base }

def expectMerge (pool : ConceptPool) (base : Name) (canonical : Name) :
    MetaM Unit := do
  match (pool.find? (inventedNs ++ base)).bind (·.mergedInto) with
  | some t =>
    unless t == canonical do
      throwError "{base} merged into {t}, expected {canonical}"
  | none => throwError "{base} did not merge at birth"

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let mut canonical : Array ProbeTarget := #[]
  for p in preds do
    if let some t ← probeTargetOfConst p.name then
      canonical := canonical.push t
  IO.println s!"{canonical.size} canonical predicates extracted from {carrier}"
  let known ← collectKnown [carrier]
  IO.println s!"grounding pool: {known.size} {carrier}.* lemmas"
  -- `simp only`, not `simp`: the default set's `dual_isLoop_iff_isColoop`
  -- fights the `IsColoop` unfold and loops.
  let ctx : ProbeCtx :=
    { known
      extraRungs := #["tauto", "aesop",
        "simp only [Matroid.dep_iff, Matroid.IsColoop, Matroid.dual_dual, \
Matroid.singleton_dep, Set.singleton_subset_iff, and_comm, and_assoc, \
and_left_comm]"] }
  let mut proposals : Array ConceptProposal := #[]
  for (base, defn) in
      [(`loop_element, ``cand_loop_element),
       (`is_loop_specialized, ``cand_is_loop_specialized),
       (`loop_as_dual_coloop, ``cand_loop_as_dual_coloop),
       (`cocircuit_as_dual_circuit, ``cand_cocircuit_as_dual_circuit),
       (`is_cocircuit_def, ``cand_is_cocircuit_def),
       (`dep_invented, ``cand_dep_invented)] do
    proposals := proposals.push (← proposalFromDef base defn)
  -- The D5 dualization operator, applied to a canonical circuit predicate.
  let some circuitT ← probeTargetOfConst ``Matroid.IsCircuit
    | throwError "no probe target for IsCircuit"
  let some dualCircuit ← mkDualizeProposal circuitT
    | throwError "dualization operator failed on IsCircuit"
  proposals := proposals.push dualCircuit

  IO.println ""
  IO.println "── the tower, at birth ──"
  let (pool, corpus, stats) ← inventRound ctx {} {} canonical proposals
  IO.println s!"  {stats.describe}"
  unless stats.refused == 0 do throwError "no candidate should be refused"
  unless stats.degenerate == 0 do throwError "no candidate is degenerate"
  unless stats.aliased == 7 do
    throwError "every tower brick (and the dualized circuit) should merge \
at birth, got {stats.aliased} of 7"
  expectMerge pool `loop_element ``Matroid.IsLoop
  expectMerge pool `is_loop_specialized ``Matroid.IsLoop
  expectMerge pool `loop_as_dual_coloop ``Matroid.IsLoop
  expectMerge pool `cocircuit_as_dual_circuit ``Matroid.IsCocircuit
  expectMerge pool `is_cocircuit_def ``Matroid.IsCocircuit
  expectMerge pool `dep_invented ``Matroid.Dep
  expectMerge pool `dual_IsCircuit ``Matroid.IsCocircuit
  unless (← auditInvented pool).isEmpty do
    throwError "the audit flagged a gate-admitted concept"
  IO.println ""
  IO.println s!"corpus: {corpus.facts.size} kernel-certified bridge facts — \
the tower's bricks, as theorems"
  IO.println "the synonym tower merges at birth; test 1 behaves as specified"
