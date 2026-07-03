import Eureka

/-!
Deterministic chain test: `=`-shaped transitive grounding. An invented
definition — `twice n = 2 * n`, a concept the library doesn't have — is
conjectured equal to `n + n`. Delta-unfolding does not close this: after
unfolding, `2 * n = n + n` is `Nat.two_mul`, a theorem, not a reflexivity
— so the defeq-grounding rungs honestly fail, along with the rest of the
direct ladder (simp and omega don't see through an unknown definition).
The chain rung closes it by composing the definitional step
(`twice n = 2 * n`, refl) with the known library bridge via `Eq.trans`;
the certificate names the bridge, and the result still passes the gate.
This is the `=` counterpart of the iff chaining exercised on the matroid
synonym tower (`MatroidStub.lean`), and a first taste of the concept
lifecycle: an invented definition, grounded against the library.
Run with `lake env lean ChainStub.lean`.
-/

open Lean Eureka.Runtime

/-- An invented concept: not in the library under this name. -/
def twice (n : Nat) : Nat := 2 * n

/-- The conjecture: the invented concept equals a form one theorem away
from its definition. -/
def conjecture : Prop := ∀ n : Nat, twice n = n + n

#eval show MetaM Unit from do
  let stmt := (← getConstInfo ``conjecture).value!
  let known ← collectKnown [`Nat]
  IO.println s!"grounding pool: {known.size} Nat.* lemmas"
  -- The direct ladder is honest: nothing on it proves this.
  match ← hunt known #[] stmt with
  | .stillOpen => IO.println s!"  ? {← Meta.ppExpr stmt} — open on the direct ladder"
  | .proved _ rung _ => throwError "expected stillOpen, but rung '{rung}' proved it"
  | .refuted cex => throwError "expected stillOpen, but refuted: {cex}"
  -- The chain rung: a refl step composed with a known bridge by Eq.trans.
  let some (pf, bridge) ← tryKnownChain known stmt tryRefl
    | throwError "chain rung failed to ground the invented definition"
  unless bridge == ``Nat.two_mul do
    throwError "expected the bridge to be Nat.two_mul, got {bridge}"
  let some f ← commitFact { name := `disco.twice_ground, stmt, proof := pf }
    | throwError "the gate refused the chained certificate"
  IO.println s!"  ✓ {← Meta.ppExpr stmt} — chained via {bridge}, kernel-gated as {f.name}"
  IO.println "eq-chaining behaves as specified"
