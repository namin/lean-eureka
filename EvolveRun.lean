import Eureka

/-!
The population, live: templates, the specializer meta-heuristic, and the
LLM — one agent among many, competing for budget on worth like everyone
else. Its move is to birth heuristics; their discoveries pay it parent
credit. Requires the `aws` CLI with Bedrock access.
Run with `lake env lean EvolveRun.lean`.
-/

open Lean Eureka.Runtime

#eval show MetaM Unit from do
  let templates := [identityH, commH, idemH, assocH, distribH, mixerH].map Agent.ofConj
  let agents := templates ++
    [specializerH, llmOracleAgent (Eureka.LLM.invoke Eureka.LLM.defaultConfig)]
  let corpus ← evolve agents { generations := 3, judgeBudget := 50, perAgentCap := 25 }
  IO.println ""
  IO.println s!"final corpus ({corpus.facts.size} facts):"
  for f in corpus.facts do
    IO.println s!"  {f.name} : {toString (← Meta.ppExpr f.stmt)}"
