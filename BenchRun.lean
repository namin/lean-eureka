import EurekaMathlib

/-!
# The standing benchmark (DESIGN_RECORD R2)

The frozen *generator*: the deterministic matroid and graph
configurations regenerate their open sets — the conjectures the system
wants to prove and cannot — and the pin (counts + sentinels) makes
corpus drift loud instead of silent. The symbolic ladders then run over
the corpus and print the closure table; `REPORT_BENCH.md` records the
baseline, and future prover work moves the numbers or it didn't happen.

Corpus version: **1** (pins below). A machinery change that shifts the
regenerated corpus must bump the version and re-baseline the report.

Deterministic; no LLM. Run with `lake env lean BenchRun.lean` (not in
CI: needs the Mathlib build, ~30 min).
-/

open Lean Meta Eureka.Runtime

set_option linter.unusedSimpArgs false

def benchLadders (tag : String) (deep : ProbeCtx) (refuter : Refuter)
    (base : Corpus) (opens : Array (Conjecture × Name × Nat)) :
    MetaM Unit := do
  let mut closed := 0
  let mut refuted := 0
  let mut stillOpen := 0
  let mut corpus := base
  for (c, _, _) in opens do
    let (corpus', o) ← escalate deep corpus c refuter
    corpus := corpus'
    match o with
    | .admitted _ note =>
      closed := closed + 1
      IO.println s!"  ✓ [{tag}] {toString (← ppExpr c.stmt)} ({note})"
    | .refuted w =>
      refuted := refuted + 1
      IO.println s!"  ✗ [{tag}] {toString (← ppExpr c.stmt)} ({w})"
    | _ => stillOpen := stillOpen + 1
  IO.println s!"{tag} deep ladder: {closed} closed, {refuted} refuted, \
{stillOpen} open of {opens.size}"

#eval show MetaM Unit from do
  -- ── matroid corpus ──
  let mPreds ← collectPredicates `Matroid
  let mut mCanonical : Array ProbeTarget := #[]
  for p in mPreds do
    if let some t ← probeTargetOfConst p.name then
      mCanonical := mCanonical.push t
  let mKnown ← collectKnown [`Matroid]
  let mRungs : Array String := #["tauto",
    "simp only [Matroid.dep_iff, Matroid.IsColoop, Matroid.dual_dual, \
Matroid.singleton_dep, Set.singleton_subset_iff, and_comm, and_assoc, \
and_left_comm]"]
  let mCtx : ProbeCtx :=
    { known := mKnown, extraRungs := mRungs, probeHeartbeats := some 5000
      probeEdges := false, inventedTargetWindow := some 12 }
  let mRefuter : Refuter := fun stmt => do
    let usedInv := (stmt.getUsedConstants.filter
      (inventedNs.isPrefixOf ·)).map toString
    let pre := if usedInv.isEmpty then "" else
      s!"unfold {String.intercalate " " usedInv.toList}; "
    refuteByInstances matroidRefuterSimpArgs (mkConst ``Nat)
      matroidInstances stmt (pre := pre)
  let mr ← evolveWith
    [dualizerAgent mCanonical, compounderAgent, inventedImplAgent mCanonical]
    { generations := 3, judgeBudget := 25, perAgentCap := 20,
      knownPrefixes := [`Matroid], refuter := mRefuter,
      probeCtx := some mCtx, canonical := mCanonical }
  IO.println ""
  IO.println s!"matroid corpus: {mr.opens.size} opens"
  -- The pin (version 1).
  unless mr.opens.size == 16 do
    throwError "matroid corpus drift: expected 16 opens, got \
{mr.opens.size} — bump the corpus version and re-baseline"
  unless mr.opens.any (fun e =>
      e.1.stmt.getUsedConstants.contains (inventedNs ++ `dual_IsRkFinite)) do
    throwError "matroid sentinel missing: dual_IsRkFinite family"

  -- ── graph corpus ──
  let gPreds ← collectPredicates `SimpleGraph
  let mut gCanonical : Array ProbeTarget := #[]
  for p in gPreds do
    if let some t ← probeTargetOfConst p.name then
      gCanonical := gCanonical.push t
  let gKnown ← collectKnown [`SimpleGraph]
  let gRungs : Array String := #["tauto",
    "simp only [SimpleGraph.isClique_compl, SimpleGraph.isIndepSet_compl, \
SimpleGraph.isClique_iff, SimpleGraph.isIndepSet_iff, compl_compl, \
and_comm, and_assoc, and_left_comm]"]
  let gCtx : ProbeCtx :=
    { known := gKnown, extraRungs := gRungs, probeHeartbeats := some 5000
      probeEdges := false, inventedTargetWindow := some 12 }
  let gr ← evolveWith
    [complementerAgent gCanonical, graphCompounderAgent,
     inventedImplAgent gCanonical]
    { generations := 3, judgeBudget := 20, perAgentCap := 20,
      knownPrefixes := [`SimpleGraph], refuter := graphRefuter,
      probeCtx := some gCtx, canonical := gCanonical }
  IO.println ""
  IO.println s!"graph corpus: {gr.opens.size} opens"
  unless gr.opens.size == 13 do
    throwError "graph corpus drift: expected 13 opens, got \
{gr.opens.size} — bump the corpus version and re-baseline"
  unless gr.opens.any (fun e =>
      e.1.stmt.getUsedConstants.contains (inventedNs ++ `compl_IsVertexCover)) do
    throwError "graph sentinel missing: compl_IsVertexCover family"

  -- ── the ladders ──
  IO.println ""
  IO.println "━━ the closure table ━━"
  let mDeepKnown ← collectKnown [`Matroid, `Set]
  let mkSafe := fun (canonical : Array ProbeTarget) => do
    let mut safe : Array Name := #[]
    for t in canonical do
      if let some ci := (← getEnv).find? t.name then
        if let some v := ci.value? then
          let mut b := v
          while b.isLambda do
            b := b.bindingBody!
          if b.getAppFn.isConst then
            safe := safe.push t.name
    pure safe
  let mSafe ← mkSafe mCanonical
  let mDeep : ProbeCtx :=
    { known := mDeepKnown
      transparent := fun n => inventedNs.isPrefixOf n || mSafe.contains n
      extraRungs := mRungs ++ #["aesop"], composeDepth := 3 }
  benchLadders "matroid" mDeep mRefuter mr.corpus mr.opens
  let gDeepKnown ← collectKnown [`SimpleGraph, `Set]
  let gSafe ← mkSafe gCanonical
  let gDeep : ProbeCtx :=
    { known := gDeepKnown
      transparent := fun n => inventedNs.isPrefixOf n || gSafe.contains n
      extraRungs := gRungs ++ #["aesop"], composeDepth := 3 }
  benchLadders "graph" gDeep graphRefuter gr.corpus gr.opens
  IO.println ""
  IO.println "benchmark: corpus v1 pinned and measured"
