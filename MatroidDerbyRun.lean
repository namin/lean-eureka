import EurekaMathlib

/-!
The operator derby (DESIGN_WORTH acceptance test 5): the yield table's
fit criterion, run through the population engine.

Two concept-proposing agents over the matroid canonical pool: the
dualizer (whose products largely ground as certified aliases — the
duality involution) and the conjunction operator (whose products are
almost entirely unmergeable boolean novelty). Under pay-certainty
pricing, `dualize > conj` in final worth is the criterion fixed in the
design: if the prices don't produce that ordering, the prices are
wrong. The conjunction agent's novel births alone should earn ≈ 0 —
and with enough attention, the kill rule should take it.

Deterministic; no LLM. Run with `lake env lean MatroidDerbyRun.lean`
(not in CI: needs the Mathlib build).
-/

open Lean Meta Eureka.Runtime

set_option linter.unusedSimpArgs false

def dualizerAgent (canonical : Array ProbeTarget) : Agent where
  name := `dualizer
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for t in canonical do
      if let some p ← mkDualizeProposal t then
        unless (← getEnv).contains (inventedNs ++ p.name) do
          out := out.push (.concept p)
    return out

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

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let mut canonical : Array ProbeTarget := #[]
  for p in preds do
    if let some t ← probeTargetOfConst p.name then
      canonical := canonical.push t
  let known ← collectKnown [carrier]
  let ctx : ProbeCtx :=
    { known
      extraRungs := #["tauto",
        "simp only [Matroid.dep_iff, Matroid.IsColoop, Matroid.dual_dual, \
Matroid.singleton_dep, Set.singleton_subset_iff, and_comm, and_assoc, \
and_left_comm]"]
      probeHeartbeats := some 2000
      probeEdges := false
      inventedTargetWindow := some 12 }
  let r ← evolveWith [dualizerAgent canonical, conjAgent canonical]
    { generations := 2, judgeBudget := 10, perAgentCap := 25,
      knownPrefixes := [carrier], probeCtx := some ctx, canonical }
  let w := fun (a : Name) => r.ledger.worth {} (fun _ => #[]) a
  IO.println ""
  IO.println s!"derby: dualizer {w `dualizer} vs conj {w `conj}"
  let cd := r.ledger.counts `dualizer
  let cc := r.ledger.counts `conj
  IO.println s!"  dualizer: {cd.conceptsAliased} aliased, {cd.conceptsNovel} novel"
  IO.println s!"  conj: {cc.conceptsAliased} aliased, {cc.conceptsNovel} novel"
  unless w `dualizer > w `conj do
    throwError "the fit criterion: dualize > conj, got \
{w `dualizer} ≤ {w `conj}"
  unless r.dead.contains `conj do
    throwError "unpriced novelty should take the conj agent to the kill rule"
  unless (← auditInvented r.pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  IO.println "the derby orders as the yield table predicts"
