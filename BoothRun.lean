import Eureka

/-!
The full pipeline against a live LLM: template heuristics discover the base
corpus, then the booth asks the model (Claude on Bedrock) to propose beyond
the templates. Requires the `aws` CLI with Bedrock access; everything the
model returns is untrusted and passes through the same gate.
Run with `lake env lean BoothRun.lean`.
-/

open Lean Eureka.Runtime

#eval show MetaM Unit from do
  let corpus ← discover
    [identityH, commH, idemH, assocH, distribH, mixerH]
    (generations := 2)
  let corpus ← booth (Eureka.LLM.invoke Eureka.LLM.defaultConfig)
    { rounds := 3, perRound := 8 } corpus
  IO.println ""
  IO.println s!"final corpus ({corpus.facts.size} facts):"
  for f in corpus.facts do
    IO.println s!"  {f.name} : {toString (← Meta.ppExpr f.stmt)}"
