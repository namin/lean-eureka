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

Budgets are env-overridable (defaults in parentheses):
`EUREKA_PRED_POOL` (10) predicates in the pool, `EUREKA_GENERATIONS` (3),
`EUREKA_JUDGE_BUDGET` (30), `EUREKA_PER_AGENT_CAP` (30),
`EUREKA_BOOTH_ROUNDS` (2), `EUREKA_BOOTH_PER_ROUND` (6). E.g.

  EUREKA_BOOTH_ROUNDS=5 EUREKA_BOOTH_PER_ROUND=10 \
  lake env lean MatroidDiscoRun.lean

The corpus materializes to `../eureka-corpus` when present
(`EUREKA_CORPUS_DIR` overrides; empty disables).
-/

open Lean Eureka.Runtime

/-- A `Nat` from the environment, or the default (also on a non-numeric
value — budgets are conveniences, not inputs worth failing over). -/
def envNat (name : String) (default : Nat) : IO Nat := do
  return (← IO.getEnv name).bind (·.toNat?) |>.getD default

-- The command ceiling, raised for loop overhead (reply parsing, dedup
-- scans, printing) across the booth rounds; the prover stays pinned to
-- `judgeHeartbeats` per judgment regardless (see `Eureka/Loop.lean`).
set_option maxHeartbeats 400000000 in
#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let pool := preds.toList.take (← envNat "EUREKA_PRED_POOL" 10) |>.toArray
  IO.println s!"predicate pool ({pool.size} of {preds.size} extracted):"
  for p in pool do
    let shape := if p.shape == PredShape.element then "element" else "set"
    IO.println s!"  {p.name} ({shape})"
  let agents := [implicationsAgent carrier pool, exclusionsAgent carrier pool,
                 dualityAgent pool, singletonAgent pool]
  let corpus ← evolve agents
    { generations := (← envNat "EUREKA_GENERATIONS" 3),
      judgeBudget := (← envNat "EUREKA_JUDGE_BUDGET" 30),
      perAgentCap := (← envNat "EUREKA_PER_AGENT_CAP" 30),
      knownPrefixes := [carrier] } {}
  let corpus ← booth (Eureka.LLM.invoke Eureka.LLM.defaultConfig)
    { rounds := (← envNat "EUREKA_BOOTH_ROUNDS" 2),
      perRound := (← envNat "EUREKA_BOOTH_PER_ROUND" 6),
      knownPrefixes := [carrier],
      render := renderMatroidPrompt pool } corpus
  IO.println ""
  IO.println s!"final corpus ({corpus.facts.size} facts, every one kernel-gated):"
  for f in corpus.facts do
    IO.println s!"  {f.name} : {toString (← Meta.ppExpr f.stmt)}"
  materializeIfConfigured "Matroid" "DiscoRun" corpus
    (header := "Producing run: MatroidDiscoRun.lean — template agents over \
extracted Matroid predicates plus LLM booth rounds.")
