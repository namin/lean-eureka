import EurekaMathlib

/-!
Escalation over a real open class (DESIGN_DEPTH acceptance test 1).

The deterministic grand-run configuration — dualizer, compounder,
invented-implications, no LLM — whose invented-vocabulary conjectures
mostly land open on the cheap ladder (the grand run's `invented_impls`
died at 33/34 open). The escalation pass re-judges the open set with
the deep ladder: ambient budget, uncut `aesop`/`tauto`, composition
depth 3, and a grounding pool widened beyond `Matroid.*` to the `Set`
lemmas the invented bodies are actually made of. Pre-registered
criterion: escalation admits or certifiably refutes at least one
conjecture the cheap ladder left open, every admission through
`commitFact`, audit clean. Deterministic; no LLM. Run with
`lake env lean MatroidDepthRun.lean` (not in CI: needs the Mathlib
build).
-/

open Lean Meta Eureka.Runtime

set_option linter.unusedSimpArgs false

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let mut canonical : Array ProbeTarget := #[]
  for p in preds do
    if let some t ← probeTargetOfConst p.name then
      canonical := canonical.push t
  let known ← collectKnown [carrier]
  let deepKnown ← collectKnown [carrier, `Set]
  IO.println s!"pools: cheap {known.size}, deep {deepKnown.size} \
(Set.* joins the grounding pool under escalation)"
  let cheapRungs : Array String := #["tauto",
    "simp only [Matroid.dep_iff, Matroid.IsColoop, Matroid.dual_dual, \
Matroid.singleton_dep, Set.singleton_subset_iff, and_comm, and_assoc, \
and_left_comm]"]
  let ctx : ProbeCtx :=
    { known, extraRungs := cheapRungs
      probeHeartbeats := some 5000
      probeEdges := false
      inventedTargetWindow := some 12 }
  -- Under escalation the *canonical* definitional layer is transparent
  -- too (P2's delta-expandable philosophy applied to the domain): with
  -- `Coindep` expanded to `M✶.Indep`, implication goals reach the
  -- compose rung's head-indexed candidates directly. Safety rule:
  -- expand only defs whose body is const-headed — structure projections
  -- (`IsBase`, `Indep`) expand to proj-headed terms that defeat
  -- head-indexing the same way beta-redexes did.
  let mut safeCanon : Array Name := #[]
  for t in canonical do
    if let some ci := (← getEnv).find? t.name then
      if let some v := ci.value? then
        let mut b := v
        while b.isLambda do
          b := b.bindingBody!
        if b.getAppFn.isConst then
          safeCanon := safeCanon.push t.name
  IO.println s!"deep transparency: invented + \
{safeCanon.toList} (const-headed canonical defs)"
  let safeCanon' := safeCanon
  let deepCtx : ProbeCtx :=
    { known := deepKnown
      transparent := fun n =>
        inventedNs.isPrefixOf n || safeCanon'.contains n
      extraRungs := cheapRungs ++ #["aesop",
        "simp [Matroid.dep_iff, Set.singleton_subset_iff]"]
      composeDepth := 3 }
  let refuter : Refuter := fun stmt => do
    let usedInv := (stmt.getUsedConstants.filter
      (inventedNs.isPrefixOf ·)).map toString
    let pre := if usedInv.isEmpty then "" else
      s!"unfold {String.intercalate " " usedInv.toList}; "
    refuteByInstances matroidRefuterSimpArgs (mkConst ``Nat)
      matroidInstances stmt (pre := pre)
  let r ← evolveWith
    [dualizerAgent canonical, compounderAgent, inventedImplAgent canonical]
    { generations := 4, judgeBudget := 25, perAgentCap := 20,
      knownPrefixes := [carrier], refuter, probeCtx := some ctx, canonical,
      escalationBudget := 8, deepCtx := some deepCtx }
  IO.println ""
  let ci := r.ledger.counts `invented_impls
  IO.println s!"invented_impls: {ci.admitted} admitted \
({ci.admittedDeep} deep/escalated), {ci.refuted} refuted, {ci.opens} open \
events"
  let escalatedFacts := r.ledger.events.filter fun e =>
    e.kind == .factAdmitted .escalated
  let escRefuted := r.corpus.facts.filter fun f =>
    f.name.toString.endsWith "_refuted"
  IO.println s!"escalated admissions: {escalatedFacts.size}; certified \
refutations in corpus: {escRefuted.size}"
  -- Test 1's pre-registered criterion.
  unless escalatedFacts.size ≥ 1 do
    throwError "escalation should close at least one conjecture the cheap \
ladder left open (got {escalatedFacts.size}) — if this fires, the deep \
ladder needs work, and that is the finding"
  unless (← auditInvented r.pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  IO.println ""
  IO.println "escalation closes real opens; depth run behaves as specified"
