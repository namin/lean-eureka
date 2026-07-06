# REPORT: the standing benchmark (lean-eureka)

DESIGN_RECORD R2. The corpus is a frozen *generator* — the
deterministic matroid and graph configurations regenerate their open
sets, pinned by count and sentinel (`BenchRun.lean`); drift is a loud
version bump, never silent. This file records the baseline; future
prover work moves these numbers or it didn't happen.

## Corpus v2 (current)

Full-coverage generator (every proposed pair judged): the corpus is the
*complete* residue, immune to the enumeration-rotation sensitivity that
made v1 a sample (a kit change shifted corpus size, which shifted the
rotation offsets, which changed *which pairs were ever judged* — found
when the graph count moved the wrong way).

| family | opens | pin verified |
|---|---|---|
| matroid | 14 | ✓ (two runs) |
| graph | 17 | ✓ (two runs) |

**The kit enrichment (DESIGN_RESOLVE K1/K2, claim B1)** certifiably
refuted 12 statements at generation that v1 left open — the entire
`elem_dual_IsBase` family among them. The decisive fix was not the new
witnesses but a depth-2 bug the kits exposed: the refuter's `unfold`
prefix collected invented names from the statement only, so a lifted
concept's *parent* stayed folded and simp went blind
(`inventedUnfoldNames`, now transitively closed, shared by every
refuter). New witnesses (`freeOn`/`loopyOn` on two elements, the
reversed unique-base, set-literal disequality lemmas; edge and path
graphs) carried the rest.

## Corpus v1 (superseded)

| family | opens | pin verified |
|---|---|---|
| matroid | 16 | ✓ (two runs) |
| graph | 13 | ✓ (two runs) |

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
| matroid v2 (14) | **1** | 0 | 13 |
| graph v2 (17) | **0** | 0 | 17 |

The one closure is `dual_IsBase a → Coindep a`
(`escalated: composed: IsBasis.indep + IsBase.isBasis_ground`),
reproducing REPORT_DEPTH's result — the benchmark's first consistency
check with the prior record passes.

**The number to beat: 1 of 31 (3.2%).** The residue is what every
report since the grand run has described: false-but-unwitnessed
implications (richer witness kits would refute them) and true
existential/neighborhood statements (repair with domain-tuned prompts,
or the stepper with domain move sets, would prove them). REPORT_PROVE
showed repair closing exactly this statement class on a hand-pinned
corpus; running the LLM ladders over *this* corpus is the natural next
measurement.

## The repair phase (`BenchProveRun.lean`, live — claims B3/B4)

The LLM repair rung over the v2 residue: 23 statements attempted, 8
deferred by the 40-call meter, 39 calls, **transcript verified
entry-for-entry against the meter** (B4 — R1's machinery in live use).
Result: **1 closure** (`dual_IsBase → Coindep`, round 1) — B3's letter
satisfied, but the honest reading is sharper: that statement is the one
the deep *symbolic* ladder also closes, so repair's marginal
contribution over symbolic escalation on this corpus is zero.

The transcripts explain much of it: **10 of 39 calls returned no
extractable text** — the model spent its entire token budget in a
thinking block, and the client's extractor found nothing. A quarter of
the repair budget evaporated into a client gap, diagnosed only because
the transcripts existed. The next lever on this benchmark is therefore
not a smarter prover but a fixed client (retry-on-empty extraction, or
a separate thinking budget), then re-measure.

## Reproduction

```
lake env lean BenchRun.lean        # corpus v2 + symbolic table (deterministic)
lake env lean BenchProveRun.lean   # the repair phase (Mathlib + Bedrock)
```
