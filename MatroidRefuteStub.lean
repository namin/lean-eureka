import EurekaMathlib

/-!
The refuter, first slice: the matroid implication sweep with a
counterexample search. `MatroidStub.lean` reports 42 candidate
implications honestly open because nothing in the domain can refute; here
each conjecture is first instantiated at concrete matroids — `freeOn {0}`,
`loopyOn {0}`, `uniqueBaseOn {0} {0,1}` (which has both a coloop and a
loop), `emptyOn` — and the *negation* of the instance is proved by simp
with the constructions' characterization lemmas. A refutation is therefore
kernel-certifiable, and this file commits each one through the gate: false
conjectures die with the same evidence standard by which true ones live.

The refuter is partial and honest about it: 32 of the 42 opens die, each
gate-certified; the 10 survivors are conjectures false only on *infinite*
matroids (the `→ IsRkFinite` family — a finite witness pool provably
cannot touch them) or needing witnesses with non-singleton circuits and
minimality reasoning beyond simp. The remaining opens are the genuine
frontier, not a pile of falsehoods. Run with
`lake env lean MatroidRefuteStub.lean` (not in CI: needs the Mathlib
build).
-/

open Lean Eureka.Runtime

-- The refuter's simp vocabulary is a union over all instances; per-goal
-- unused entries are by design.
set_option linter.unusedSimpArgs false

/-- Concrete witnesses, as named definitions so the refuter's simp call
can unfold them by name. -/
def mFree : Matroid ℕ := Matroid.freeOn {0}
def mLoopy : Matroid ℕ := Matroid.loopyOn {0}
def mUB : Matroid ℕ := Matroid.uniqueBaseOn {0} {0, 1}
def mEmpty : Matroid ℕ := Matroid.emptyOn ℕ
def sEmpty : Set ℕ := ∅
def s0 : Set ℕ := {0}
def s1 : Set ℕ := {1}
def s01 : Set ℕ := {0, 1}

/-- `uniqueBaseOn`'s base characterization is conditional on `I ⊆ E`;
discharge it once, at our instance, so simp can use it unconditionally. -/
theorem ubOn_isBase_iff {B : Set ℕ} :
    (Matroid.uniqueBaseOn ({0} : Set ℕ) {0, 1}).IsBase B ↔ B = {0} :=
  Matroid.uniqueBaseOn_isBase_iff (by simp)

/-- The refuter's simp vocabulary: unfold the witnesses, characterize the
predicates at the concrete constructions, reduce duality and singletons. -/
def refuterSimpArgs : Array String := #[
  "mFree", "mLoopy", "mUB", "mEmpty", "sEmpty", "s0", "s1", "s01",
  "ubOn_isBase_iff",
  "Matroid.dep_iff", "Matroid.coindep_def", "Matroid.isCocircuit_def",
  "Matroid.loopyOn_isLoop_iff", "Matroid.uniqueBaseOn_isLoop_iff",
  "← Matroid.singleton_dep",
  "Matroid.isColoop_iff_forall_mem_isBase",
  "Matroid.empty_not_isCircuit", "Matroid.singleton_isCircuit",
  "not_imp"]

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let pool := preds.toList.take 10 |>.toArray
  let known ← collectKnown [carrier]
  IO.println s!"{pool.size} predicates, {known.size} {carrier}.* grounding lemmas"
  let instances : Array (Expr × Expr × String) := #[
    (mkConst ``mFree,  mkConst ``sEmpty, "M := freeOn {0}, X := ∅"),
    (mkConst ``mFree,  mkConst ``s0,     "M := freeOn {0}, X := {0}"),
    (mkConst ``mLoopy, mkConst ``sEmpty, "M := loopyOn {0}, X := ∅"),
    (mkConst ``mLoopy, mkConst ``s0,     "M := loopyOn {0}, X := {0}"),
    (mkConst ``mUB,    mkConst ``sEmpty, "M := uniqueBaseOn {0} {0,1}, X := ∅"),
    (mkConst ``mUB,    mkConst ``s0,     "M := uniqueBaseOn {0} {0,1}, X := {0}"),
    (mkConst ``mUB,    mkConst ``s1,     "M := uniqueBaseOn {0} {0,1}, X := {1}"),
    (mkConst ``mUB,    mkConst ``s01,    "M := uniqueBaseOn {0} {0,1}, X := {0,1}"),
    (mkConst ``mFree,  mkNatLit 0,       "M := freeOn {0}, e := 0"),
    (mkConst ``mLoopy, mkNatLit 0,       "M := loopyOn {0}, e := 0"),
    (mkConst ``mUB,    mkNatLit 0,       "M := uniqueBaseOn {0} {0,1}, e := 0"),
    (mkConst ``mUB,    mkNatLit 1,       "M := uniqueBaseOn {0} {0,1}, e := 1"),
    (mkConst ``mEmpty, mkNatLit 0,       "M := emptyOn ℕ, e := 0")]
  let mut corpus : Corpus := {}
  let mut admitted := 0
  let mut refuted := 0
  let mut opens : Array String := #[]
  for P in pool do
    for Q in pool do
      if P.name != Q.name && P.shape == Q.shape then
        let (corpus', outcome, pretty) ← withCurrHeartbeats do
          let c ← mkImplConjecture carrier P Q
          let pretty := toString (← Meta.ppExpr c.stmt)
          -- refute first — cheap relative to the hunt, and certified
          if let some (negStmt, pf, witness) ←
              refuteByInstances refuterSimpArgs (mkConst ``Nat) instances c.stmt then
            let nm ← freshName (c.name.appendAfter "_refuted")
            match ← commitFact { name := nm, stmt := negStmt, proof := pf } with
            | some f =>
              let corpus' := { corpus with facts := corpus.facts.push f }
              pure (corpus', Outcome.refuted witness, pretty)
            | none => pure (corpus, Outcome.refusedAtGate, pretty)
          else
            let (corpus', outcome) ← judge known corpus c
            pure (corpus', outcome, pretty)
        corpus := corpus'
        match outcome with
        | .admitted _ note =>
          admitted := admitted + 1
          IO.println s!"  ✓ {pretty} — admitted ({note})"
        | .refuted witness =>
          refuted := refuted + 1
          IO.println s!"  ✗ {pretty} — refuted ({witness}), gate-certified"
        | .stillOpen => opens := opens.push pretty
        | .refusedAtGate => IO.println s!"  ! {pretty} — REFUSED at gate"
  IO.println ""
  IO.println s!"sweep: {admitted} admitted, {refuted} refuted (each refutation \
kernel-gated as a fact about a concrete witness), {opens.size} open"
  for o in opens do
    IO.println s!"  ? {o}"
  IO.println s!"corpus: {corpus.facts.size} kernel-certified facts"
  unless admitted == 2 do
    throwError "expected the 2 certified implication edges, got {admitted}"
  unless refuted == 32 do
    throwError "expected 32 certified refutations, got {refuted}"
  unless opens.size == 10 do
    throwError "expected 10 honest opens, got {opens.size}"
  unless corpus.facts.size == admitted + refuted do
    throwError "every refutation should have passed the gate"
  IO.println "refuter behaves as specified"
