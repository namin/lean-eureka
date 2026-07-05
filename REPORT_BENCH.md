# REPORT: the standing benchmark (lean-eureka)

DESIGN_RECORD R2. The corpus is a frozen *generator* — the
deterministic matroid and graph configurations regenerate their open
sets, pinned by count and sentinel (`BenchRun.lean`); drift is a loud
version bump, never silent. This file records the baseline; future
prover work moves these numbers or it didn't happen.

## Corpus v1

| family | opens | pin verified |
|---|---|---|
| matroid (dualizer + compounder + invented-implications, 3 gens) | 16 | ✓ (two runs) |
| graph (complementer + compounder + invented-implications, 3 gens) | 13 | ✓ (two runs) |

Sentinels: the `dual_IsRkFinite` family (matroid), the
`compl_IsVertexCover` family (graph). Note the corpus is *post-cheap,
post-refuter*: everything the 5000-heartbeat ladder or the witness kits
could decide is already gone — during generation the cheap ladder even
composes the old flagship (`IsCocircuit K → dual_Dep K`, a four-lemma
proof) in-loop.

## Baseline closure table (deep symbolic ladder)

Escalation configuration: ambient budget, `Set.*` pools, safe canonical
transparency, composition depth 3, `aesop`, the induction rungs.

| family | closed | refuted | open |
|---|---|---|---|
| matroid (16) | **1** | 0 | 15 |
| graph (13) | **0** | 0 | 13 |

The one closure is `dual_IsBase a → Coindep a`
(`escalated: composed: IsBasis.indep + IsBase.isBasis_ground`),
reproducing REPORT_DEPTH's result — the benchmark's first consistency
check with the prior record passes.

**The number to beat: 1 of 29 (3.4%).** The residue is what every
report since the grand run has described: false-but-unwitnessed
implications (richer witness kits would refute them) and true
existential/neighborhood statements (repair with domain-tuned prompts,
or the stepper with domain move sets, would prove them). REPORT_PROVE
showed repair closing exactly this statement class on a hand-pinned
corpus; running the LLM ladders over *this* corpus is the natural next
measurement.

## Reproduction

```
lake env lean BenchRun.lean   # Mathlib, deterministic, ~30 min
```
