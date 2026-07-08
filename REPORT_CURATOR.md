# REPORT: the curator ablation (lean-eureka)

Built and run to `DESIGN_CURATOR.md`: the LLM in Lenat's seat over a
symbolic mutation stream, restricted by type to attention — boosts,
damps, flags, mutation *choices*, escalation nominations, labels.
L7-i's ablation: the standing configuration (six hand-written template
agents + the specializer chain + genome-backed round-robin mutation)
run twice on Nat with identical seeds and budgets, without and with
the curator. Model `us.anthropic.claude-sonnet-5` via Bedrock; 6
curator calls (one per generation); transcript
`transcripts/curator-ablation.jsonl`. No NL proposer rung — the
curator tends symbolic proposers only. Every "admitted" below is
kernel-gated; no curator action has an admission path (W4).

## Setup

`CuratorRun.lean`: 6 generations, judge budget 40,
`seedGenomes := templateGenomes` (comm/assoc/idem/distrib),
`mutationRoundRobin := 1`, exploration floor on, no refuter, no
escalation. Control and experiment differ in exactly one field:
`curatorCall`.

## The numbers

|  | control | curated |
|---|---|---|
| corpus (kernel-gated facts) | 35 | 36 |
| final population | 23 | 28 |
| dead | 0 | 0 |
| mutants born | 6 | 8 |
| mutant judged proposals | **0** | 17 |
| curator calls | — | 6 |

Curator actions over 6 calls: 15 boosts (explore_gcd ×4, probe_gcd ×3,
specializer ×3, explore_max/min ×2 each, distrib ×2, probe_max/min ×1
each — counted per target above where tallied), 9 damps (mixer ×3;
probe_add/mul/sub, explore_add/mul via singles; identity, idem, the
distribL mutant), 2 flags (both of mixer's admissions:
`disco.mix_max_gcd_1`, `disco.mix_gcd_max_1` — pay cancelled), 1
escalation nomination (explore_gcd's open), 2 labels, 3 inapplicable
mutate attempts (substOp on full-pool genomes), 3 mutate attempts on
agents with no genome (dropped correctly), 1 prose paragraph (dropped
by the grammar).

Worth deltas, control → curated, same underlying outcomes: mixer 0.50
→ **0.00** (damped, both facts' pay cancelled); explore_gcd 0.67 →
0.92; probe_gcd 0.75 → 1.00; distrib 0.55 → 0.66; probe_add/mul 0.50 →
0.38; explore_add/mul 0.55 → 0.43. No kills in either arm — six
generations leave most agents under `minTrials`.

## What the curator did with the seat

Its attention allocation was coherent and consistent across
generations: it backed the gcd frontier (the family holding the run's
only open conjecture and its freshest admissions), suppressed the
refuted-heavy explorers and the shallow mixer, and used its two labels
well —

> `disco.mul_distrib_gcd_1`: genuinely new cross-op distributivity,
> worth deeper follow-up
>
> `distrib`: gcd/add and gcd/mul and gcd/max/min combos consistently
> refuted, retire those op pairs

The first label is coherent taste but an over-claim: the fact is the
hand-written distrib agent's mul-over-gcd law, present in *both* arms
and grounded in Mathlib — "new" is curator enthusiasm, which is
exactly what L7-iii's calibration instrument exists to score. The
second label is correct and actionable (it matches the refutation
record), and is the kind of judgment the retired `restrictPool`
refinement wants as input.

Its best output was refused by its own cage: one reply led with a
prose analysis — probe_max/min/gcd landing the same
idempotent-absorption pattern, idem-family mutants "clearly wasted
since idempotence fails there structurally" for add/mul/sub — which is
*correct mathematical judgment*, and the parser dropped it as
non-action, as designed. The closed menu buys safety by type and pays
for it in expressiveness; labels are the sanctioned channel and it
partially routed the same content there.

## The mutation stream

The starkest line in the table: control's six round-robin mutants
produced **zero judged proposals**. Round-robin fell down a single
lineage (`restrictPool` on idem, dropping one operation at a time),
and a restriction of a full-pool parent proposes only statements the
parent already attempted — every proposal a free verbatim repeat.
The curator-less baseline is structurally redundant, not just
unlucky.

The curated arm's mutation pressure spread across the comm, distrib,
and idem lineages and substituted toward gcd, and one mutant was
genuinely generative: the distribL pair-family mutant earned a
grounded admission the hand templates never proposed
(`a * (b - c) = a * b - a * c`, Nat.mul_sub_left_distrib) plus **15
certified refutations** — a kernel-checked map of exactly where
distributivity fails across the operation pairs, which is settled
knowledge the economy pays for (W2). One run-note wart: curator-chosen
births and round-robin births were indistinguishable in this run's log
(the attribution print was added immediately after — `⚙ chose mutate`
— so the next run separates them cleanly).

## Interpretation (separate from the facts above)

1. **Six generations of Nat cannot show a corpus delta, and didn't**
   (35 vs 36). What the ablation *does* show is the seat working:
   allocation moved coherently toward the earning frontier, the
   shallowest agent was economically zeroed, and the mutation stream
   went from structurally-redundant drift to a family that produced
   the run's only mutant discoveries. Whether allocation converts to
   corpus advantage needs longer horizons and a harder domain — the
   matroid run, with the refuter on, is the real test.
2. **The grammar's safety/expressiveness trade is now measured.** The
   curator's richest reasoning arrived as prose and was dropped by
   design. That is the right default — but it argues for keeping
   `label` first-class in the report pipeline (narration is where
   Lenat's sense-making lived), not for widening the action surface.
3. **Calibration is the next instrument that matters.** The curator's
   taste tracked ground truth in this run except for one enthusiasm
   error on a Mathlib-grounded rediscovery. Scoring labels and boosts
   against later use (the royalties design) turns "the curator seems
   sensible" into a number.
4. **The round-robin baseline needs teeth** before the ablation is
   fair: earned-aware `restrictPool` and unexplored-op `substOp` (the
   L4 refinement deferred from slice one) would make the control more
   than a redundancy generator.

## Reproduction

```
lake env lean CuratorStub.lean   # acceptance tests 1–6 (CI, canned)
lake env lean CuratorRun.lean    # the ablation (Bedrock; 6 curator calls)
transcripts/curator-ablation.jsonl
```
