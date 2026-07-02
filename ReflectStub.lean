import Eureka

/-!
Deterministic test of booth stage two: a canned "LLM" proposes, in order,
(1) a heuristic that violates the rule policy (spawns a process) — rejected
before compilation; (2) after feedback, a broken heuristic — rejected with
the elaboration error fed back; (3) a working heuristic proposing `a ^ 2 =
a * a` — installed, fired, and its conjecture admitted through the fact
gate. Round 2 then produces (4) a heuristic whose conjectures are false or
duplicates — installed and fired, with nothing reaching the corpus.
Run with `lake env lean ReflectStub.lean`.
-/

open Lean Eureka.Runtime

def evil : String :=
"```lean
fun _corpus => do
  let _ ← IO.Process.output { cmd := \"echo\", args := #[\"pwned\"] }
  return #[]
```"

def broken : String :=
"```lean
fun corpus => return corpus.nonexistentField
```"

def good : String :=
"```lean
fun _corpus => do
  let natTy := mkConst ``Nat
  let stmt ← withLocalDeclD `a natTy fun a => do
    let sq ← mkAppM ``HPow.hPow #[a, mkNatLit 2]
    let mul ← mkAppM ``HMul.hMul #[a, a]
    mkForallFVars #[a] (← mkEq sq mul)
  return #[{ name := Name.mkSimple \"pow_two\", stmt, origin := `stub }]
```"

def junk : String :=
"```lean
fun _corpus => do
  let natTy := mkConst ``Nat
  let mut out := #[]
  -- false: ∀ a, a * 2 = a
  let f1 ← withLocalDeclD `a natTy fun a => do
    mkForallFVars #[a] (← mkEq (← mkAppM ``HMul.hMul #[a, mkNatLit 2]) a)
  out := out.push { name := Name.mkSimple \"junk1\", stmt := f1, origin := `stub }
  -- duplicate of the round-1 discovery: ∀ a, a ^ 2 = a * a
  let f2 ← withLocalDeclD `a natTy fun a => do
    let sq ← mkAppM ``HPow.hPow #[a, mkNatLit 2]
    mkForallFVars #[a] (← mkEq sq (← mkAppM ``HMul.hMul #[a, a]))
  out := out.push { name := Name.mkSimple \"junk2\", stmt := f2, origin := `stub }
  return out
```"

#eval show MetaM Unit from do
  let counter ← IO.mkRef 0
  let scripts := #[evil, broken, good, junk]
  let call := fun (_ : String) => do
    let i ← counter.get
    counter.set (i + 1)
    if h : i < scripts.size then
      pure (Except.ok scripts[i])
    else
      pure (Except.error "no more canned responses")
  let corpus ← boothRules call { rounds := 2, retries := 2 } {}
  IO.println ""
  IO.println s!"final corpus: {corpus.facts.toList.map (·.name)}"
  unless corpus.facts.size == 1 do
    throwError "expected exactly 1 admitted fact, got {corpus.facts.size}"
  let pretty := toString (← Meta.ppExpr corpus.facts[0]!.stmt)
  unless pretty == "∀ (a : Nat), a ^ 2 = a * a" do
    throwError "unexpected fact: {pretty}"
  IO.println "rule booth behaves as specified"
