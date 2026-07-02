import Eureka

/-!
Booth stage two, live: templates discover the base corpus, then the LLM
writes heuristic *code* — elaborated, policy-checked, compiled, installed,
and fired, with every proposed fact still passing the fact gate. Requires
the `aws` CLI with Bedrock access.
Run with `lake env lean ReflectRun.lean`.
-/

open Lean Eureka.Runtime

#eval show MetaM Unit from do
  let corpus ← discover
    [identityH, commH, idemH, assocH, distribH, mixerH]
    (generations := 2)
  let corpus ← boothRules (Eureka.LLM.invoke Eureka.LLM.defaultConfig)
    { rounds := 2, retries := 2 } corpus
  IO.println ""
  IO.println s!"final corpus ({corpus.facts.size} facts):"
  for f in corpus.facts do
    IO.println s!"  {f.name} : {toString (← Meta.ppExpr f.stmt)}"
