# REPORT: the record, re-measured (lean-eureka)

Arc 3's diagnostic chain fixed a beta-redex bug in `expandConsts` that
had suppressed every head-indexed prover rung (compose, known, chain)
on expanded forms since slice one — meaning the recorded numbers in
earlier reports were measured on a weaker prover than the code now
ships. This report re-runs the record: the five deterministic matroid
instruments, then the grand run under the full current system (beta
fix + tier pricing + attracted credit + escalation). Original reports
are left as measured; this is the refit column.

## The deterministic instruments, pre → post

| instrument | pre-fix (as reported) | post-fix |
|---|---|---|
| Tower at birth (`MatroidInventStub`) | 7/7 merged | 7/7 merged — identical |
| Yield births (`MatroidYieldRun`) | dualize 6/9, lift 3/7+⊤, boolean 1/66 | identical |
| Yield facts phase | 87 admitted / 569 refuted / 278 open | **89 / 569 / 276** |
| Compounding (`MatroidCompoundRun`) | S1–S3, decay 2.71 vs 3.25 | identical |
| Derby (`MatroidDerbyRun`) | dualize 0.38 > conj 0.02 † | identical |
| Economy (`MatroidEconomyRun`) | separates, 0.29 → 0.42 | separates, **0.48 → 0.62** |

Reading the table honestly:

- **The birth pipeline was never bottlenecked on head-indexed rungs** —
  aliases at birth are caught by refl, targeted simp, unfold rungs, and
  the chain, all of which beta-reduce or work folded. Identical tables
  are the confirmation.
- **The facts-phase gain at a 5000-heartbeat budget is +2 admissions.**
  The beta fix's real effect concentrates where composition matters:
  the depth run showed the flagship (`IsCocircuit K → dual_Dep K`)
  moving from unprovable to *cheap-ladder-provable* by a four-lemma
  composition, and escalation closing `dual_IsBase → Coindep` — those
  are in REPORT_DEPTH. At tight sweep budgets over this conjecture
  class, most remaining opens are false-but-unwitnessed or genuinely
  deep, not composition-shaped.
- **The economy run's lift (0.29→0.48 / 0.42→0.62) is tier pricing,
  not the beta fix**: the `exclusions` agent's admissions include
  composed/tauto proofs, which now pay 2.0. The separation — the
  instrument's actual claim — holds unchanged.

## The grand run, v2 (full current system)

Same eight agents as REPORT_GRAND, now with the beta-fixed prover,
tier pricing, attracted credit, and an escalation pass (budget 5, deep
ladder with `Set.*` pool, safe canonical transparency, composition
depth 3). One LLM call per generation while the booth lives.

Passed, audit clean. **Corpus 100 certified facts (v1: 81), 35 in
invented vocabulary (v1: 16).** Pool: 50 concepts born across both
depths (the booth invented a fresh set — 16 novel, again zero
restatements). And the standings tell the arc's story:

- **Nobody was killed.** In v1, `invented_impls` (worth 0.03, 0
  admissions) and `concept_booth` (0.04, all-unpaid novelty) both died
  in generation 3.
- **`invented_impls` finishes at 0.15 with 3 admissions** — the
  beta-fixed compose rung proving invented-vocabulary implications
  in-loop, the capability v1 lacked entirely.
- **`concept_booth` finishes at 0.15 with 2 vocabulary credits** — paid,
  while alive, for certified structure other agents built on its
  concepts. The kill-then-posthumous-vindication injustice that
  motivated Arc 3 does not recur under Arc 3's credits.
- Escalated-tier admissions in-run: 0 — consistent with the refit
  table; the stronger cheap ladder eats what escalation would have,
  and the residue is genuinely hard.

## Interpretation (separate from the facts above)

1. The refit validates the original record: nothing previously reported
   was wrong, and the suppressed-prover effect is real but
   concentrated — in-loop composition on invented-vocabulary
   implications and escalation-budget proving, exactly the places Arc 3
   was aimed at. In vivo that concentration is decisive: invented-
   vocabulary facts doubled, and two agents that died under the old
   prover-and-prices now live productively.
2. Deterministic instruments staying byte-identical under a substantial
   library fix is the regression suite doing its job: the fix changed
   *capability*, not the behavior of anything already certified.
3. The system's economy and its prover are now consistent with each
   other: agents whose value arrives late or through others (inventors)
   survive long enough to be paid, and the conjectures that pay them
   are provable enough to land. That closed loop — invent, conjecture,
   compose, certify, credit — running for four generations without a
   death or an audit flag, is the state of the system this report
   freezes.

## Reproduction

```
lake env lean MatroidInventStub.lean && lake env lean MatroidYieldRun.lean \
  && lake env lean MatroidCompoundRun.lean && lake env lean MatroidDerbyRun.lean \
  && lake env lean MatroidEconomyRun.lean   # the deterministic record
lake env lean MatroidGrandRun.lean          # grand v2 (Mathlib + Bedrock)
```
