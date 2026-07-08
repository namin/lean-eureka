import Eureka

/-!
The curator ablation (DESIGN_CURATOR L7-i), live on the Nat domain: the
standing configuration — symbolic proposers + mutation stream — run
twice with identical seeds and budgets, without and with the LLM in
Lenat's seat. No NL proposer rung: the curator tends a symbolic stream.

Instruments: admissions per judge slot, mutants born and their yield,
kill decisions, and (with the curator) boosts/damps/flags against what
the agents went on to earn. Requires Bedrock credentials; NOT in CI.
Curator transcript to `transcripts/curator-ablation.jsonl` (R1).
Run with `lake env lean CuratorRun.lean`.
-/

open Lean Eureka.Runtime

set_option maxHeartbeats 400000000 in
#eval show MetaM Unit from do
  let templates := [identityH, commH, idemH, assocH, distribH, mixerH].map Agent.ofConj
  let base : EvolveConfig :=
    { generations := 6, judgeBudget := 40, perAgentCap := 25,
      seedGenomes := templateGenomes, mutationRoundRobin := 1 }
  IO.println "════ control: symbolic + round-robin mutation, no curator ════"
  let control ← evolveWith (templates ++ [specializerH]) base
  IO.println ""
  IO.println "════ experiment: same population, the LLM in Lenat's seat ════"
  let ccall ← Eureka.LLM.withTranscript "transcripts/curator-ablation.jsonl"
    "curator" (Eureka.LLM.invoke {})
  let cured ← evolveWith (templates ++ [specializerH])
    { base with curatorCall := some ccall }
  IO.println ""
  IO.println s!"control:    {control.corpus.facts.size} facts, \
{control.dead.size} dead, {control.population.size} agents"
  IO.println s!"experiment: {cured.corpus.facts.size} facts, \
{cured.dead.size} dead, {cured.population.size} agents"
  unless cured.labels.isEmpty do
    IO.println "curator notes:"
    for (n, note) in cured.labels do
      IO.println s!"  {n}: {note}"
