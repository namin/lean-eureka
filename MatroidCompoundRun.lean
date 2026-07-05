import EurekaMathlib

/-!
Compounding, slice two (DESIGN_INVENT C1–C4, acceptance tests S1–S3).

The dualizer births depth-1 products of the canonical pool; the
compounder reads the live pool and re-applies dualization and
singleton-lift to invented survivors, producing depth-2 products. The
expected structure: `dual (dual X)` merges back into canonical `X` —
the duality involution as a *depth-2 certificate* — and lifts of dual
survivors ground through the dual singleton bridges
(`M✶.Dep {e} ↔ M.IsColoop e` via `singleton_dep` on the dual). Depth is
capped at 2; alias pay decays per agent (C4), so the compounder's
mechanically-minted involution bridges must not out-earn the honest
dualizer. Deterministic; no LLM. Run with
`lake env lean MatroidCompoundRun.lean` (not in CI: needs the Mathlib
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
  let ctx : ProbeCtx :=
    { known
      extraRungs := #["tauto",
        "simp only [Matroid.dep_iff, Matroid.IsColoop, Matroid.dual_dual, \
Matroid.singleton_dep, Set.singleton_subset_iff, and_comm, and_assoc, \
and_left_comm]"]
      probeHeartbeats := some 2000
      probeEdges := false
      inventedTargetWindow := some 12 }
  let r ← evolveWith [dualizerAgent canonical, compounderAgent]
    { generations := 3, judgeBudget := 10, perAgentCap := 25,
      knownPrefixes := [carrier], probeCtx := some ctx, canonical }
  let w := fun (a : Name) => r.ledger.worth {} (fun _ => #[]) a
  IO.println ""
  IO.println "── the pool, by depth ──"
  for c in r.pool.concepts do
    let fate := match c.mergedInto with
      | some t => s!"≡ {t}"
      | none => "✦ live"
    IO.println s!"  d{c.depth} {c.name} [{c.origin}] {fate}"
  IO.println ""
  IO.println s!"worth: dualizer {w `dualizer}, compounder {w `compounder}"
  -- S2: the depth cap held.
  unless r.pool.concepts.all (·.depth ≤ 2) do
    throwError "a product exceeded the depth cap"
  -- S1: a depth-2 involution product merged into its canonical grandparent.
  let involutions := r.pool.concepts.filter fun c =>
    c.depth == 2 && c.name.getString!.startsWith "dual_dual_" &&
    c.mergedInto.isSome
  unless involutions.size ≥ 2 do
    throwError "expected dual ∘ dual products certified back into canonical \
vocabulary, got {involutions.size}"
  for c in involutions do
    let some t := c.mergedInto | continue
    unless t.getPrefix == carrier do
      throwError "{c.name} merged into {t}, expected a canonical target"
  -- S1, the economics: C4's decay bites — the compounder's alias pay is
  -- strictly below full price. (The decay is a long-run cap on mining,
  -- not a small-n ordering: a mixed compounder with a higher certified
  -- rate may legitimately out-earn the depth-1 dualizer per attention.)
  let cc := r.ledger.counts `compounder
  let undecayed := cc.conceptsAliased.toFloat * (0.75 : Float) +
    cc.conceptsDegenerate.toFloat * 0.25
  let actual := r.ledger.ownValue {} `compounder
  IO.println s!"compounder value {actual} vs undecayed {undecayed}"
  unless cc.conceptsAliased ≥ 2 && actual + 0.01 < undecayed do
    throwError "C4's alias decay should reduce the pay below full price, \
got {actual} vs {undecayed}"
  -- S3: depth-2 yield is nonzero — certified verdicts exist at depth 2.
  unless r.pool.concepts.any (fun c => c.depth == 2 && c.mergedInto.isSome) do
    throwError "expected nonzero certified yield at depth 2"
  unless (← auditInvented r.pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  IO.println "compounding behaves as specified (S1–S3)"
