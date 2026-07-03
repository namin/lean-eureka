import Eureka

/-!
Deterministic booth test: a canned "LLM" whose two rounds exercise every
path — admission (refl, grounded, and past omega's linear ceiling via the
case-split rung), refutation, definitional merging, verbatim-repeat
skipping, and unparseable output. No credentials, CI-able.
Run with `lake env lean BoothStub.lean`.
-/

open Lean Eureka.Runtime

def round1 : String :=
"∀ (a b : Nat), min a b = min b a
∀ (a b : Nat), a - b + b = a
∀ (n : Nat), n + 0 = n
∀ (n : Nat), n - 0 = n
∀ (a b : Nat), a ++ b = b ++ a
this line is not a conjecture and is silently dropped as prose"

def round2 : String :=
"∀ (a b : Nat), min a b = min b a
∀ (a b : Nat), max a b = max b a
∀ (a b : Nat), min a b * max a b = a * b"

#eval show MetaM Unit from do
  let counter ← IO.mkRef 0
  let call := fun (_ : String) => do
    let i ← counter.get
    counter.set (i + 1)
    pure (Except.ok (if i == 0 then round1 else round2))
  let corpus ← booth call { rounds := 2, perRound := 5 } {}
  let names := corpus.facts.toList.map (·.name)
  IO.println ""
  IO.println s!"final corpus: {names}"
  -- round 1: min-comm and n+0 admitted; a-b+b=a refuted; n-0 merged into
  -- n+0; the ++ line unparseable; the prose line dropped. round 2: min-comm
  -- skipped verbatim; max-comm admitted; min·max = a·b admitted (the
  -- nonlinear one — the split rung, past omega's ceiling). Total: 4 facts.
  unless corpus.facts.size == 4 do
    throwError "expected 4 admitted facts, got {corpus.facts.size}"
  let pretty ← corpus.facts.mapM fun f =>
    return toString (← Meta.ppExpr f.stmt)
  unless pretty.toList ==
      ["∀ (a b : Nat), min a b = min b a",
       "∀ (n : Nat), n + 0 = n",
       "∀ (a b : Nat), max a b = max b a",
       "∀ (a b : Nat), min a b * max a b = a * b"] do
    throwError "unexpected corpus contents: {pretty}"
  IO.println "booth behaves as specified"
