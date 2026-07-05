import EurekaMathlib

/-!
The generalization run (DESIGN_GRAPH claims 1–5): the whole stack on a
second carrier. Extraction, the complement operator and its compounder,
`inventedImplAgent` (unchanged, from the matroid layer — deliberately),
the graph witness kit's refuter, the economy, and escalation, on
`SimpleGraph`. The pre-registered rhymes with the matroid record: the
complement involution grounds at birth (`compl_IsClique ≡ IsIndepSet`),
depth-2 `compl_compl_X` merges back into canonical `X`, the kit
certifies refutations, the audit stays clean. Deterministic; no LLM.
Run with `lake env lean GraphRun.lean` (not in CI: needs the Mathlib
build).
-/

open Lean Meta Eureka.Runtime

set_option linter.unusedSimpArgs false

#eval show MetaM Unit from do
  let carrier := `SimpleGraph
  let preds ← collectPredicates carrier
  IO.println s!"claim 1 — extraction: {preds.size} predicates from {carrier}:"
  for p in preds do
    IO.println s!"  {p.name}"
  let mut canonical : Array ProbeTarget := #[]
  for p in preds do
    if let some t ← probeTargetOfConst p.name then
      canonical := canonical.push t
  let known ← collectKnown [carrier]
  IO.println s!"grounding pool: {known.size} {carrier}.* lemmas"
  let cheapRungs : Array String := #["tauto",
    "simp only [SimpleGraph.isClique_compl, SimpleGraph.isIndepSet_compl, \
SimpleGraph.isClique_iff, SimpleGraph.isIndepSet_iff, compl_compl, \
and_comm, and_assoc, and_left_comm]"]
  let ctx : ProbeCtx :=
    { known, extraRungs := cheapRungs
      probeHeartbeats := some 5000
      probeEdges := false
      inventedTargetWindow := some 12 }
  let deepKnown ← collectKnown [carrier, `Set]
  let deepCtx : ProbeCtx :=
    { known := deepKnown
      extraRungs := cheapRungs ++ #["aesop"]
      composeDepth := 3 }
  let r ← evolveWith
    [complementerAgent canonical, graphCompounderAgent,
     inventedImplAgent canonical]
    { generations := 3, judgeBudget := 20, perAgentCap := 20,
      knownPrefixes := [carrier], refuter := graphRefuter,
      probeCtx := some ctx, canonical,
      escalationBudget := 5, deepCtx := some deepCtx }
  IO.println ""
  IO.println "── the pool ──"
  for c in r.pool.concepts do
    let fate := match c.mergedInto with
      | some t => s!"≡ {t}"
      | none => "✦ live"
    IO.println s!"  d{c.depth} {c.name} [{c.origin}] {fate}"
  -- Claim 2: the involution grounds at birth.
  let mergedInto := fun (base : Name) =>
    (r.pool.find? (inventedNs ++ base)).bind (·.mergedInto)
  unless mergedInto `compl_IsClique == some `SimpleGraph.IsIndepSet do
    throwError "claim 2: compl_IsClique should merge into IsIndepSet, \
got {mergedInto `compl_IsClique}"
  unless mergedInto `compl_IsIndepSet == some `SimpleGraph.IsClique do
    throwError "claim 2: compl_IsIndepSet should merge into IsClique, \
got {mergedInto `compl_IsIndepSet}"
  -- Claim 3: compounding rhymes — a depth-2 involution product merged
  -- back into canonical vocabulary.
  unless r.pool.concepts.any (fun c =>
      c.depth == 2 && c.mergedInto.any (·.getPrefix == carrier)) do
    throwError "claim 3: expected a depth-2 compl ∘ compl product \
certified back into canonical vocabulary"
  -- Claim 4: the witness kit certifies refutations.
  let refutations := r.corpus.facts.filter fun f =>
    f.name.toString.endsWith "_refuted"
  unless refutations.size ≥ 1 do
    throwError "claim 4: the graph witness kit should certify at least \
one refutation"
  -- Claim 5: the economy carries over; audit clean.
  let cc := r.ledger.counts `complementer
  unless cc.conceptsAliased ≥ 2 do
    throwError "claim 5: the complementer should earn certified aliases"
  unless (← auditInvented r.pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  IO.println ""
  IO.println s!"corpus: {r.corpus.facts.size} kernel-certified facts \
({refutations.size} refutations); complementer aliased \
{cc.conceptsAliased}"
  IO.println "the stack generalizes: claims 1–5 hold on SimpleGraph"
