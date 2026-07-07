# REPORT: the order domain (lean-eureka, third carrier)

The generalization question, round two — and harder this time. Matroids
and graphs are *carrier-shaped* (`Matroid α`, `SimpleGraph α`: the
domain is a value argument); order theory is *instance-shaped*
(`IsAtom : ∀ {α} [PartialOrder α] [OrderBot α], α → Prop` — the domain
is a typeclass context, and every predicate carries a different one).
The run answers: does the stack survive a domain that has no carrier
value at all? All five pre-registered claims (OrderRun.lean's header)
hold; the surfaced assumptions are recorded below, claim-6 style. Every
"certified" is a kernel-gated fact. Deterministic; no LLM.

## The run (`OrderRun.lean`)

**Claim 1 — extraction + canonicalization generalize.** The root scan
found 36 element-shaped instance predicates; **canonicalization over the
ambient class admitted 12**, with no curated list — the domain-membership
test is elaboration itself (`fun α [BooleanAlgebra α] a => (P a : Prop)`
either elaborates or the predicate is not in the domain): `IsAtom`,
`IsCoatom`, `IsBot`, `IsTop`, `IsMin`, `IsMax`, `SupIrred`, `SupPrime`,
`InfIrred`, `InfPrime`, and two unplanned admissions, `IsCompactElement`
and `IsComplemented`. Each gets a uniform wrapper `BA.P` declared at run
time (plain `addDecl`, outside the reserved `Invented` namespace — the
audit boundary is untouched). Grounding pool: 957 lemmas *mentioning*
the raw predicates (`collectKnownMentioning`; see assumption 2).

**Claim 2 — the involution grounds at birth.**
`compl_IsAtom ≡ IsCoatom` (grounded: `isAtom_compl`) and
`compl_IsCoatom ≡ IsAtom` (grounded: `isCoatom_compl`) — the exact
analog of `dual_IsCircuit ≡ IsCocircuit` and `compl_IsClique ≡
IsIndepSet`, third carrier, certificates naming the library bridges.
Four more merges the design did not pre-register, certified by simp on
expanded forms with no library bridge at all: `compl_IsBot ≡ IsMax`,
`compl_IsTop ≡ IsBot`, `compl_IsMin ≡ IsMax`, `compl_IsMax ≡ IsBot`.

**Claim 3 — compounding rhymes.** Four depth-2 involution products
merged back into canonical vocabulary (`compl_compl_SupIrred ≡ SupIrred`,
likewise `InfIrred`, `IsCompactElement`, `IsComplemented`) — the
`dual_dual_Dep ≡ Dep` pattern, same machinery, same depth cap.

**Claim 4 — the refuter generalizes.** The Bool/Bool² kit certified
four refutations of false invented-vocabulary implications (e.g.
`IsMax a → SupIrred aᶜ`, refuted at `α := Bool, a := true`). The kit's
first rung is `decide` — both witnesses are computable Boolean algebras,
so the kernel evaluates the unfolded instance outright; the simp
vocabulary is the fallback.

**Claim 5 — the economy carries over.** The complementer earned 8
certified aliases; the compounder 4; `invented_impls` was **killed by
the economy** (worth 0.04 — 46 opens, 4 refutations, nothing admitted),
the first death of a stock agent in a domain run, and a fair verdict:
on this carrier its conjectures outrun the prover. Audit clean.

**Corpus: 16 kernel-certified facts** (8 alias bridges from depth 1,
4 involution bridges from depth 2, 4 refutations).

## The discoveries

- **`compl_InfPrime ≡ compl_InfIrred`** — the system noticed that
  inf-prime and inf-irreducible collapse in Boolean algebras (the
  classical distributivity fact), *through the complement lens*,
  certified by simp on expanded forms. It was never told about
  distributivity.
- **The live survivors are the unnamed vocabulary**: `compl_SupIrred`
  (mathematically inf-irreducibility carried by `ᶜ` — Mathlib names the
  `OrderDual` transport, `infIrred_toDual`, but has no complement form),
  `compl_InfIrred`, `compl_IsCompactElement` ("cocompact" elements),
  `compl_IsComplemented`. The last is mathematically ⊤-degenerate (in a
  Boolean algebra everything is complemented) — the degeneracy probe
  could not certify it, an honest prover-ceiling mark, not a novelty.
- The bridge `compl_SupIrred ≡ InfIrred` — true, and unnamed in
  Mathlib — stayed *open* through escalation: proving it needs de
  Morgan reasoning no ladder rung composes yet. It is the order
  domain's flagship open, the exact analog of the matroid arc's
  pre-`IsCocircuit → dual_Dep` state.

## Surfaced assumptions (the arc's data, claim-6 style)

1. **The uniform-carrier assumption.** Everything downstream of
   extraction assumes one carrier type for the pool. Instance-shaped
   domains satisfy it via **canonicalization** — runtime-declared
   uniform wrappers over an ambient class, membership decided by
   elaboration. New per-domain *move*, core untouched.
2. **`collectKnown` is namespace-prefix-based.** Order vocabulary is
   scattered at the root (`isAtom_compl` lives in no namespace), so the
   domain needed a mentions-based collector (`collectKnownMentioning`).
3. **Wrappers inherit the no-equation-lemmas disease.** `BA.*` wrappers
   are raw `addDecl` definitions: simp cannot unfold them by name, and
   the invented-only unfold prefix left them folded — the first run's
   kit certified *zero* refutations. `orderUnfoldPre` closes over both
   namespaces (the `inventedUnfoldNames` fix, one namespace over).
4. **Kit tuning stays empirical.** An ambiguous simp-lemma name
   (`not_imp` vs `Classical.not_imp`) silently broke every simp
   fallback until qualified — found only by running.

## Interpretation (separate from the facts above)

1. **The stack survives losing the carrier value.** The entire
   per-domain surface is 228 lines — canonicalization included — and
   extraction, probes, verdicts, merges, economy, escalation, and
   `inventedImplAgent` ran unchanged. "Carrier" now provably means
   *any context that makes the predicates elaborate*, value or
   instance.
2. **Involution-concentrates-value, third confirmation.** Complement
   grounded 6 of 12 at depth 1 and 4 of 4 at depth 2; its unmerged
   products are exactly the interesting vocabulary. Three carriers,
   same law.
3. The bottleneck reproduces on cue: 46 opens, 0 escalated closures —
   the system invents faster than it proves on every carrier it
   touches. `compl_SupIrred ≡ InfIrred` is the cleanest possible next
   target for prover work: elementary, true, unnamed, and one de Morgan
   step out of reach.

## Reproduction

```
lake env lean OrderRun.lean   # claims 1–5 (Mathlib, deterministic, ~4 min)
```
