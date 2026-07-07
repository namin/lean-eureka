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
a separate thinking budget), then re-measure. (Done — postscript below.)

## Postscript: the client fix, measured

The re-measurement the paragraph above asked for: five configurations
of the repair rung over the same corpus v2, one variable at a time.
Transcripts for every run are archived under `transcripts/`.

| run | client configuration | closed | attempted | deferred | no-text calls | contaminated replies |
|---|---|---|---|---|---|---|
| 1 | Sonnet 5, thinking, 16k (baseline above) | 1 | 23 | 8 | 10/39 | 8 |
| 2 | Sonnet 5, thinking off | 0 | 19 | 12 | 0/38 | 23/38 |
| 3 | Sonnet 4.6, thinking off | 0 | 19 | 12 | 0/38 | 19/38 |
| 4 | Sonnet 5, thinking, 32k + hardened harness | 1 | 22 | 9 | 13/39 | 0 |
| 5 | **Sonnet 5, thinking at `effort: medium`, 32k + hardened harness** | **1** | 20 | 11 | **3/39** | **0** |

Findings, in causal order:

- **The no-text failures were not a plumbing bug.** Doubling
  `max_tokens` (run 4) did not reduce them: on goals it cannot crack,
  the model's deliberation expands to fill any budget — measured, 31993
  of 32000 output tokens spent thinking, no answer ever started. The
  lever is the `effort` cap, not headroom; `budget_tokens`, the fix the
  paragraph above guessed at, no longer exists on this model family.
- **Thinking is load-bearing for output discipline.** With thinking off
  (runs 2–3), half the replies open with prose or `<answer>` tags
  despite the no-prose instruction, and nothing closes.
- **The harness was leaking calls.** `extractProofScript` now unwraps
  `<answer>` tags and code fences and strips leading/trailing prose;
  the repair prompt now warns that `Invented.*` definitions have no
  simp lemmas (`unfold`/`change`, never `simp [Invented.foo]`) — a
  transcript near-miss died on exactly that idiom.
- **The closure count is invariant.** Every configuration closes the
  same statement (`dual_IsBase → Coindep`) or nothing. Repair's
  marginal contribution over the symbolic ladder stays zero; the
  residue is proof capacity — now established across two models and
  three thinking regimes rather than assumed.

Where the client landed (`Eureka/LLM.lean`): `defaultConfig` — no
thinking, 16k — for proposal-shaped callers (the concept booth);
`proverConfig` — adaptive thinking at `effort: medium`, 32k — for the
repair rung (`BenchProveRun.lean`, `MatroidProveRun.lean`). Run 5 is
the standing configuration: the baseline's closure at a fraction of
the waste.

## Reproduction

```
lake env lean BenchRun.lean        # corpus v2 + symbolic table (deterministic)
lake env lean BenchProveRun.lean   # the repair phase (Mathlib + Bedrock)
```
