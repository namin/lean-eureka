import EurekaMathlib

/-!
The repair phase over the benchmark residue (DESIGN_RESOLVE K4): the
LLM repair rung, two calls per statement, over corpus v2's survivors —
transcripts on (their first live workout, claim B4), every closure
through the gate at the escalated tier, a hard 40-call meter (states
what it skips; no silent caps).

The corpus generators below are verbatim copies of `BenchRun.lean`'s
v2 configuration — keep in sync; the pins guard the copy.

Live LLM (≤ 40 Bedrock calls) + Mathlib; not in CI. Run with
`lake env lean BenchProveRun.lean`.
-/

open Lean Meta Eureka.Runtime

set_option linter.unusedSimpArgs false

#eval show MetaM Unit from do
  -- ── regenerate corpus v2 (keep in sync with BenchRun.lean) ──
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
  let mr ← evolveWith
    [dualizerAgent mCanonical, compounderAgent, inventedImplAgent mCanonical]
    { generations := 3, judgeBudget := 300, perAgentCap := 200,
      knownPrefixes := [`Matroid], refuter := matroidRefuterInv,
      probeCtx := some mCtx, canonical := mCanonical }
  unless mr.opens.size == 14 do
    throwError "matroid corpus drift vs v2 pin: {mr.opens.size}"
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
    { generations := 3, judgeBudget := 300, perAgentCap := 200,
      knownPrefixes := [`SimpleGraph], refuter := graphRefuter,
      probeCtx := some gCtx, canonical := gCanonical }
  unless gr.opens.size == 17 do
    throwError "graph corpus drift vs v2 pin: {gr.opens.size}"

  -- ── the repair phase, metered ──
  let calls ← IO.mkRef 0
  let raw := Eureka.LLM.invoke Eureka.LLM.defaultConfig
  let inner ← Eureka.LLM.withTranscript
    "transcripts/bench-repair.jsonl" "bench-repair" raw
  let call : String → IO (Except String String) := fun p => do
    calls.modify (· + 1)
    inner p
  let mDeepKnown ← collectKnown [`Matroid, `Set]
  let gDeepKnown ← collectKnown [`SimpleGraph, `Set]
  let mut closed := 0
  let mut attempted := 0
  let mut skipped := 0
  let mut corpusM := mr.corpus
  let mut corpusG := gr.corpus
  for (tag, opens, deepKnown) in
      [("matroid", mr.opens, mDeepKnown), ("graph", gr.opens, gDeepKnown)] do
    for (c, _, _) in opens do
      if (← calls.get) ≥ 38 then
        skipped := skipped + 1
        continue
      attempted := attempted + 1
      match ← proveByRepair call deepKnown c.stmt with
      | some (pf, rounds) =>
        let commit := { name := ← freshName c.name, stmt := c.stmt,
                        proof := pf : FactProposal }
        if let some f ← commitFact commit then
          closed := closed + 1
          if tag == "matroid" then
            corpusM := { corpusM with facts := corpusM.facts.push f }
          else
            corpusG := { corpusG with facts := corpusG.facts.push f }
          IO.println s!"  ✓ [{tag}] {toString (← ppExpr c.stmt)} \
(repair, round {rounds})"
        else
          IO.println s!"  ! [{tag}] repaired proof REFUSED at gate"
      | none => pure ()
  let total ← calls.get
  -- B4: the transcript matches the meter.
  let entries := ((← IO.FS.readFile
    "transcripts/bench-repair.jsonl").trimAscii.toString.splitOn "\n").length
  unless entries == total do
    throwError "transcript entries {entries} ≠ calls {total} (B4)"
  IO.println ""
  IO.println s!"repair over corpus v2: {closed} closed of {attempted} \
attempted ({skipped} deferred by the 40-call meter); {total} calls, \
transcript verified"
  IO.println "the repair phase: measured"
