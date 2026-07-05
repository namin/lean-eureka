import Eureka

/-!
Deterministic proof-search tests (DESIGN_PROVE acceptance tests 1, 2, 3,
5), canned transports throughout. Tests 4 and 6 — the live control and
comparison — are `MatroidProveRun.lean`.

- **Retrieval finds the needed lemma** (test 3): symbol overlap puts
  `Nat.gcd_self` in the top-k for a gcd goal.
- **The repair loop works** (test 1): `∀ n, dbl n = 2 * n` for a
  recursive, *non*-simp `dbl` is open on the full symbolic escalation
  ladder (nothing can unfold it); the canned model first returns a
  broken script, then — fed the error — the correct induction proof;
  admitted through the gate.
- **The gate refuses a poisoned proof** (test 2): a canned script that
  proves via a minted axiom elaborates, and dies at the axiom audit —
  this arc's Smoke.
- **The stepper works** (test 5): cheap moves alone fail; with the
  canned move-generator supplying the closing line at the stuck goal,
  the search assembles a proof that passes the gate.

Run with `lake env lean ProveStub.lean`.
-/

open Lean Meta Eureka.Runtime

/-- Recursive and deliberately not `@[simp]`: opaque to every symbolic
rung. -/
def dbl : Nat → Nat
  | 0 => 0
  | n + 1 => dbl n + 2

def cannedCall (responses : Array String) (counter : IO.Ref Nat)
    (prompts : IO.Ref (Array String)) : String → IO (Except String String) :=
  fun prompt => do
    prompts.modify (·.push prompt)
    let i ← counter.get
    counter.set (i + 1)
    if h : i < responses.size then return .ok responses[i]
    else return .error "out of canned responses"

#eval show MetaM Unit from do
  let known ← collectKnown [`Nat]
  IO.println "━━ test 3: retrieval ━━"
  let gcdGoal ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkForallFVars #[n] (← mkEq (← mkAppM ``Nat.gcd #[n, n]) n)
  let premises ← retrievePremises known gcdGoal
  unless premises.any (·.name == ``Nat.gcd_self) do
    throwError "Nat.gcd_self should be retrieved for a gcd goal"
  IO.println s!"  ✓ Nat.gcd_self in the top-{premises.size}"

  IO.println ""
  IO.println "━━ test 1: the repair loop ━━"
  let stmt ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkForallFVars #[n] (← mkEq (← mkAppM ``dbl #[n])
                               (← mkAppM ``HMul.hMul #[mkNatLit 2, n]))
  let conj : Conjecture := { name := `dbl_eq, stmt, origin := `test }
  let deep : ProbeCtx := { known }
  let (_, o1) ← escalate deep {} conj
  let .stillOpen := o1
    | throwError "the symbolic escalation ladder should fail on dbl_eq"
  let counter ← IO.mkRef 0
  let prompts ← IO.mkRef (#[] : Array String)
  let broken := "intro n\nomega"
  let good := "intro n\ninduction n with\n| zero => rfl\n| succ k ih => simp only [dbl]; omega"
  let some (pf, rounds) ←
      proveByRepair (cannedCall #[broken, good] counter prompts) known stmt
    | throwError "the repair loop should recover from the broken script"
  unless rounds == 2 do
    throwError "expected success on the repair round, got round {rounds}"
  let ps ← prompts.get
  unless ps.size == 2 &&
      ((ps[1]!.splitOn "previous attempt failed").length > 1) do
    throwError "the second prompt should carry the failure feedback"
  let some _ ← commitFact { name := `disco.dbl_eq, stmt, proof := pf }
    | throwError "the repaired proof should pass the gate"
  IO.println "  ✓ broken script, error fed back, repaired, kernel-gated"

  IO.println ""
  IO.println "━━ test 2: the gate refuses a poisoned proof ━━"
  addDecl <| .axiomDecl
    { name := `proveDemo.evilAx, levelParams := [], type := stmt,
      isUnsafe := false }
  let counter2 ← IO.mkRef 0
  let prompts2 ← IO.mkRef (#[] : Array String)
  let some (evilPf, _) ←
      proveByRepair (cannedCall #["exact proveDemo.evilAx"] counter2 prompts2)
        known stmt
    | throwError "the evil script should elaborate (the screen cannot catch it)"
  unless (← commitFact
      { name := `disco.dbl_evil, stmt, proof := evilPf }).isNone do
    throwError "the axiom audit must refuse the poisoned proof"
  IO.println "  ✓ elaborates, dies at the axiom audit — the gate did not grow"

  IO.println ""
  IO.println "━━ test 5: the stepper ━━"
  let stmt5 ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkForallFVars #[n] (← mkEq (← mkAppM ``dbl #[n])
                               (← mkAppM ``HAdd.hAdd #[n, n]))
  match ← proveByStepper none known stmt5 with
  | some _ => throwError "cheap moves alone should not close dbl n = n + n"
  | none => pure ()
  let counter3 ← IO.mkRef 0
  let prompts3 ← IO.mkRef (#[] : Array String)
  let mover := cannedCall
    #["induction a <;> simp only [dbl] <;> omega",
      "induction a <;> simp only [dbl] <;> omega"] counter3 prompts3
  let some pf5 ← proveByStepper (some mover) known stmt5
    | throwError "the stepper with the canned move should close it"
  let some _ ← commitFact { name := `disco.dbl_add, stmt := stmt5, proof := pf5 }
    | throwError "the stepper's proof should pass the gate"
  unless (← counter3.get) ≥ 1 do
    throwError "the move generator should have been consulted"
  IO.println "  ✓ cheap moves fail; the suggested move closes it; kernel-gated"
  IO.println ""
  IO.println "proof search behaves as specified"
