import EurekaMathlib

/-!
Matroid discovery proper, live: the population engine over template agents
derived from the extracted `Matroid` predicates, then LLM booth rounds on
top. The comparison target is the formal-disco matroid baseline
(REPORT_MATROID / REPORT_ALIGN): there, Lean was a 75s-per-probe subprocess
and grounding was post-hoc; here every admission carries its certificate at
admission time. Requires the `aws` CLI with Bedrock access for the booth
rounds (they degrade gracefully without).
Run with `lake env lean MatroidDiscoRun.lean`.
-/

open Lean Eureka.Runtime

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let pool := preds.toList.take 10 |>.toArray
  IO.println s!"predicate pool ({pool.size} of {preds.size} extracted):"
  for p in pool do
    let shape := if p.shape == PredShape.element then "element" else "set"
    IO.println s!"  {p.name} ({shape})"
  let agents := [implicationsAgent carrier pool, exclusionsAgent carrier pool,
                 dualityAgent pool, singletonAgent pool]
  let corpus ← evolve agents
    { generations := 3, judgeBudget := 30, perAgentCap := 30,
      knownPrefixes := [carrier] } {}
  let corpus ← booth (Eureka.LLM.invoke Eureka.LLM.defaultConfig)
    { rounds := 2, perRound := 6, knownPrefixes := [carrier],
      render := renderMatroidPrompt pool } corpus
  IO.println ""
  IO.println s!"final corpus ({corpus.facts.size} facts, every one kernel-gated):"
  for f in corpus.facts do
    IO.println s!"  {f.name} : {toString (← Meta.ppExpr f.stmt)}"
