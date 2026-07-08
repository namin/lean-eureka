import Eureka

/-!
The representation derby (DESIGN_HEURISTICS_NL N6), live on the Nat
domain: hand-written Lean heuristics, the specializer's born-code chain,
the code oracle (`llmOracleAgent`), and the NL rung — the ported
baseline templates plus the NL oracle — in one population, same gates,
same pricing. Heuristic representation is the independent variable;
worth is the measurement, and reach (NL admissions the code rungs never
attempted) is the headline number.

Requires Bedrock credentials; NOT in CI. Transcript to
`transcripts/nl-derby.jsonl` (DESIGN_RECORD R1).
Run with `lake env lean NLRun.lean`.

The raised command ceiling pays for loop overhead only — reply parsing,
dedup scans, printing — which a 6-generation LLM run accumulates past the
default 200k (the first live run died of exactly this at generation 4).
Judgments stay at the canonical budget: `judge` pins `judgeHeartbeats`.
-/

open Lean Eureka.Runtime

set_option maxHeartbeats 400000000 in
#eval show MetaM Unit from do
  let base := Eureka.LLM.invoke {}
  let call ← Eureka.LLM.withTranscript "transcripts/nl-derby.jsonl" "nl-derby" base
  let templates := [identityH, commH, idemH, assocH, distribH, mixerH].map Agent.ofConj
  let nlRung ← nlSeeds.mapM fun (n, b) => nlAgent call n b
  let pop := templates ++ [specializerH, llmOracleAgent call, nlOracleAgent call]
    ++ nlRung
  let res ← evolveWith pop
    { generations := 6, judgeBudget := 40, perAgentCap := 25,
      nlCall := some call, nlProposeBudget := 6 }
  IO.println ""
  IO.println s!"final corpus: {res.corpus.facts.size} facts, all kernel-gated"
  -- Reach, first cut: facts admitted from the NL rung (conjecture names
  -- carry the proposing agent's name). The full reach analysis — NL
  -- admissions absent from every code agent's attempted set — comes from
  -- the transcript + ledger in REPORT_HEURISTICS_NL.md.
  let nlFacts := res.corpus.facts.filter fun f =>
    ((toString f.name).splitOn "disco.nl").length > 1
  IO.println s!"NL-rung facts: {nlFacts.size}"
  for f in nlFacts do
    IO.println s!"  {f.name}: {toString (← Meta.ppExpr f.stmt)}"
