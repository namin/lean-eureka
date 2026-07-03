import EurekaMathlib

/-!
The refuter, first slice: the matroid implication sweep with a
counterexample search. `MatroidStub.lean` reports 42 candidate
implications honestly open because nothing in the domain can refute; here
each conjecture is first instantiated at concrete matroids — `freeOn {0}`,
`loopyOn {0}`, `uniqueBaseOn {0} {0,1}` (which has both a coloop and a
loop), `emptyOn` — and the *negation* of the instance is proved by simp
with the constructions' characterization lemmas (the refuter kit in
`EurekaMathlib/MatroidDisco.lean`). A refutation is therefore
kernel-certifiable, and `judge` commits each one through the gate: false
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

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let pool := preds.toList.take 10 |>.toArray
  let known ← collectKnown [carrier]
  IO.println s!"{pool.size} predicates, {known.size} {carrier}.* grounding lemmas"
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
          let (corpus', outcome) ← judge known corpus c matroidRefuter
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
