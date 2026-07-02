import Eureka

/-!
The discovery demo: algebraic-law heuristics over `Nat` operations, three
generations. Nothing printed as admitted was typed in by a human; nothing
enters the corpus except through the gate. `mixerH`'s conjectures are
second-generation by construction — they are built *from* admitted facts.
Run with `lake env lean Disco.lean`.
-/

open Eureka.Runtime

#eval show Lean.MetaM Unit from do
  let corpus ← discover
    [identityH, commH, idemH, assocH, distribH, mixerH]
    (generations := 3)
  IO.println ""
  IO.println "corpus:"
  for f in corpus.facts do
    IO.println s!"  {f.name} : {toString (← Lean.Meta.ppExpr f.stmt)}"
