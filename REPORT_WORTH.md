# REPORT: the worth economy (lean-eureka)

Arc 2, built to `DESIGN_WORTH.md`: the admissions-only worth function
replaced by a fold of an event ledger through a pricing table, the
exploration floor, concepts as a population proposal kind, and the
three instruments run. Every number below that says "certified" is a
kernel-gated fact; worth never touches admission — it only schedules
attention (W4).

## Setup

- `Eureka/Worth.lean`: typed event ledger (facts admitted / refuted /
  open / repeats / dups / gate refusals; concept alias / degenerate /
  novel / refused; vocabulary credits; delayed alias credit), pricing
  table (`Prices`), worth = smoothed value per unit of attention, with
  per-target alias decay and decaying returns on refutations computed
  in the fold. Counts (`AgentCounts`) are a projection — reporting,
  never pricing.
- `Eureka/Evolve.lean`: `evolveWith` returns corpus + ledger + concept
  pool; `RProposal.concept` routes through the birth gate and identity
  probe inside the population; facts in invented vocabulary go through
  the concept-aware judge (`judgeConceptFact` — `judge`'s hunt sees
  invented constants as opaque); admitted facts pay the mentioned
  concepts' inventors, and a fact linking two inventions fires re-probe
  trigger (i), whose merges pay as *delayed* credit; the exploration
  floor gives every live agent one judged proposal per generation
  before the shared budget.

## Two price-curve fits, forced by the first instrument run

The drafted table priced every dup at −0.25 and every refutation at a
flat 0.5. The very first `EvolveStub` trajectory showed both wrong:
template agents (which re-fire their enumerations every generation)
were being killed for verbatim repeats — `identity` at worth 0.00 with
5 admissions — while `junk` (falsehoods only) sat at 0.50, above every
honest prover. Verbatim repeats are now split from defeq dups and
priced at zero, and refutations pay with decaying returns
(`refutedDecay`): junk sinks to 0.14 and keeps sinking; the honest
population reorders sanely (comm/assoc 0.80, distrib 0.55, identity
0.36). Prices are data; both fixes were table edits, which is W1's
point.

## The instruments

**Test 1 — the economy experiment separates**
(`MatroidEconomyRun.lean`). The finding that motivated Arc 2, three
runs over, was that refuter-off and refuter-on produced *identical*
worth trajectories. Re-run under the ledger: control (18 open) worth
0.288; experiment (17 certified refutations + 1 open) worth **0.424**.
Refutations are visible; the trajectories separated.

**Tests 2–4, 6–7 — the deterministic suite** (`WorthStub.lean`, CI).
The ordering holds exactly — all-admitted 0.97 > all-refuted 0.22 >
all-open 0.04 > all-garbage 0.00, garbage killed, fodder alive. The
alias farmer merges 32 clones into `isEven`, is paid for the target
once, decays to 0.038, and dies. Delayed credit lands: the inventor of
the stuck pair is paid to worth 1.0 in a run where it proposed nothing
— the linker's edge (admitted by the concept-aware judge after the
unlock) fired trigger (i) and the merge credited the inventor. With
judge budget zero, the floor still gets every agent judged each
generation. The Smoke-style adversary's falsehood dies at the
refutation step, its axiom never enters a proof, and its smuggled
`Invented` def is flagged by the namespace audit.

**Test 5 — the derby orders as the yield table predicts**
(`MatroidDerbyRun.lean`). The fit criterion fixed in the design: over
the matroid pool, the dualizer (6 certified aliases — the duality
involution — plus 3 novel) finishes at worth **0.50**; the conjunction
agent (22 unmergeable novel products, 0 certificates) finishes at
**0.02 and is killed by the end of generation 1**. Pay-certainty
pricing turns the yield table's finding — value concentrates in
structure-aware operators — into agenda behavior.

## Interpretation (separate from the facts above)

1. The economy now sees what the system certifies. Every event class
   the gates produce — admissions, refutations, bridges, degeneracies,
   vocabulary facts, delayed merges — has a price, and the three
   pathologies the old function created or hid (refutation-blindness,
   starvation-by-ordering, unpriced invention) each have a regression
   instrument.
2. The instruments earned their keep immediately: two of the drafted
   prices were wrong in ways only trajectories could show, and both
   fixes were data edits. The pricing table is the seam a future
   reflective layer would propose changes through — the
   gate-one-level-up axis, still deliberately out of scope.
3. What worth still cannot see: proof *depth* (an omega-rung admission
   pays like a hard composition), and novelty that later proves
   valuable (a novel concept pays only when certified structure
   arrives — correct against noise-farming, but it means a slow deep
   invention is indistinguishable from noise until it earns). Both are
   Arc 3 questions, and both want the baseline formula's difficulty
   term — noted in the design as a second fit, only if the instruments
   demand it.

## Reproduction

```
lake env lean WorthStub.lean           # tests 2,3,4,6,7 (CI)
lake env lean EvolveStub.lean          # the repriced population (CI)
lake env lean MatroidEconomyRun.lean   # test 1 (Mathlib)
lake env lean MatroidDerbyRun.lean     # test 5 (Mathlib)
```
