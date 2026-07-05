# Worth repricing: the design (Arc 2)

The worth economy learns to see what the system actually produces —
refutations, merges, concept births, bridges — and concept proposal
moves into the population. Organized as: what this is, the constraining
facts, the decisions (W1–W7), the acceptance tests, fixed before any
code.

**Status: built.** Ledger + pricing table: `Eureka/Worth.lean`; floor,
concept routing, delayed credit, and the concept-aware judge wired into
`evolveWith` (`Eureka/Evolve.lean`, `judgeConceptFact` in
`Eureka/Concepts.lean`). Acceptance tests 2, 3, 4, 6, 7:
`WorthStub.lean` (in CI); test 1: `MatroidEconomyRun.lean`; test 5:
`MatroidDerbyRun.lean`. Two price-curve fits beyond the drafted table,
both demanded by the trajectory instrument on its first run: verbatim
re-proposals split from defeq dups and priced at zero (re-firing is
mechanical, not near-duplication — the flat dup price was killing
honest template agents), and refutations pay with decaying returns
(`refutedDecay`; flat 0.5 made falsehood-farming a stable strategy —
junk sat at 0.50 above every honest prover; under decay it sinks to
the agenda floor).

## What this is

Worth decides *attention*: `evolve` spends its judge budget in worth
order, and agents with enough trials and negligible worth are killed.
Today worth is admissions-only:

```
worth      = min 1 (admitRate × dupPenalty)
admitRate  = (admitted + ½·childAdmitted + ½) / (judged + 1)
dupPenalty = 1 − merged/(proposed + 1)
```

(`AgentStats.worth`, `Eureka/Evolve.lean`). Everything else the system
certifies is economically invisible — and after slice one, that is most
of what the system certifies.

## The facts that constrain the design

- **Refutations are invisible.** `MatroidEconomyRun`: refuter off vs on
  produces *identical* worth trajectories — 18 open vs 17
  certified-refuted + 1 open, same agenda, same deaths. A certified
  refutation is a kernel fact in the corpus; the economy cannot tell it
  from silence.
- **The yield table says where concept value lives** (REPORT_INVENT
  Run D): dualize grounded 6/9 products as certified aliases, lift 3/7
  plus a certified ⊤; conjunction grounded 0/22 and negated-conjunct
  1/44 — 65 boolean "novel" survivors of no verified standing, with
  absorption aliases hiding among them by economy configuration. A
  pricing that pays for *novelty* pays for that noise; the certified
  outcomes are where the discoveries were.
- **Concept events do not exist in the economy**: birth verdicts
  (refused / degenerate / alias / novel), spec/genl edges, and re-probe
  merges — which land *later* than the proposal that earns them (the
  InventStub unlock: trigger (i) merges a pair generations after
  birth). Delayed credit cannot be represented by in-place ratio
  updates at judge time.
- **Starvation is systematic, not incidental.** The baseline's priority
  finding: invented-vocab prove tasks created 1:3 but attempted 1:33.
  `evolve`'s strict worth-ordered spend reproduces the mechanism
  (`MatroidEconomyRun`, three times over).
- The baseline's own repriced formula (formal-disco `discovery/worth.py`)
  was multiplicative — admit × prove × novelty × difficulty, Laplace-
  smoothed, with cold-start protection. Its lesson survives even if its
  terms don't: smoothing and cold-start handling are load-bearing.

## Decisions

**W1 — The unit of account is a ledger, not a counter.** An append-only
`Ledger` of typed events (`agent`, kind, reference), written by the
loop; worth is a fold of the ledger through a *pricing table* — prices
are data, not code. *Why:* repricing experiments become table edits;
delayed credit (re-probe merges) needs an event record with provenance;
worth trajectories — the economy's instrument — become a projection of
the ledger instead of ad-hoc printing. The rejected alternative
(more `AgentStats` fields) cannot express delayed credit and turns
every pricing question into surgery on `evolve`.

**W2 — Prices: pay certainty, not novelty.** Worth becomes value per
unit of attention: `worth = clamp ((Σ event value + ½) / (attention + 1))`,
where attention counts budget actually spent on the agent (judged
proposals, concept births). Initial price vector, to be fit against the
instruments in W6:

| event | pays | note |
|---|---|---|
| fact admitted | 1.0 | grounded aliases included — grounding is discovery |
| certified refutation | 0.5 | settled knowledge, a corpus fact; strictly above open |
| open | 0.0 | silence is not evidence |
| dup / defeq merge (facts) | −0.25 | replaces the multiplicative dupPenalty |
| refused at gate | −0.5 | malformed output costs |
| concept alias-merge (bridge) | 0.75 | a theorem *and* legibility; decays to 0 on repeat (agent × canonical target) — reinvention is not farmable |
| concept degenerate (⊤/⊥) | 0.25 | certified, but the concept is dead |
| concept novel-so-far | 0.0 | novelty pays nothing until it earns |
| edge/fact in invented vocabulary | 1.0 to the concept's origin agent | concepts pay their inventor when they generate certified structure |
| child event | 0.5 × child's value | generalizes `childAdmitted` to all value, refutations included |

The two rulings that matter: refuted strictly between admitted and
open (an agent producing decidable falsehoods beats one producing
undecidable pablum — that is the economy experiment's demand), and
novel-so-far at zero (the yield table's demand — otherwise the
conjunction operator's 22 unverifiable products out-earn dualization's
6 theorems).

**W3 — An exploration floor under the ordered spend.** Every live agent
is guaranteed one judged proposal per generation before the worth-
ordered budget is spent; the floor costs at most the population size.
*Why:* strict ordering starves systematically (the 1:33 finding, the
economy run); with a floor, starvation above the floor is a priced
choice, and the kill rule — unchanged — gets the trials it needs, so
duds die *faster*, not slower. Cold start: the +½/+1 smoothing keeps
newborns above the kill threshold until `minTrials`.

**W4 — The model says nothing new, on purpose.** Worth selects which
proposals get judged; it creates no admission path. `discovery_sound`
already quantifies over an *arbitrary adversarial* interpreter, which
subsumes every scheduling policy — soundness is schedule-invariant by
construction, and Arc 2 adds no trusted surface. (Prices proposed *by
agents* — reflective repricing — would add surface; that is the
gate-one-level-up axis, explicitly deferred, per the roadmap.)

**W5 — Concepts enter the population.** `RProposal` gains
`.concept (p : ConceptProposal)`, mirroring the model's third proposal
kind; `evolve` routes it through `commitConcept` + `probeConcept`
(alias-only births, windowed targets — the run-D economy) and writes
verdict events to the ledger. The operators become agents — dualize,
singleton-lift with the matroid domain; conjunction generic — and the
concept booth becomes an agent beside `llmOracleAgent`. The `ProbeCtx`
joins `EvolveConfig`.

**W6 — Instruments fixed in advance.** (i) Worth trajectories per agent
per generation, projected from the ledger. (ii) The re-run economy
experiment: refuter off vs on must now *separate* trajectories.
(iii) The agent derby on the matroid domain: dualize-agent vs
conjunction-agent final worth, prediction `dualize > conj` from the
yield table. If the prices don't produce that ordering, the prices are
wrong — the fit criterion is decided now, before tuning.

**W7 — Bookkeeping.** Kill rule unchanged (`judged ≥ minTrials ∧
worth < killThreshold`). Alias-decay keyed by (agent, canonical
target). Smoothing constants stay `+½/+1` until an instrument says
otherwise.

## Acceptance tests (written before building)

1. **Refutations pay.** The economy experiment re-run: refuter-on and
   refuter-off worth trajectories differ, and the refuted-heavy agent
   outlives its refuter-off shadow. (Deterministic, matroid.)
2. **The ordering holds.** Synthetic agents on `Nat` — all-admitted >
   all-refuted > all-open > all-refused in final worth, asserted
   exactly.
3. **Alias-farming dies.** An agent that keeps re-proposing canonical
   vocabulary as concepts decays to the kill threshold and is killed.
4. **Delayed credit lands.** The InventStub unlock scenario inside
   `evolve`: the re-probe merge pays the merged concept's origin agent
   in a later generation, with no new proposals from it — visible in
   its trajectory.
5. **The derby orders.** Dualize-agent and conjunction-agent on the
   matroid pool: final worth `dualize > conj`, and the conjunction
   agent's 22 novel births alone earn ≈ 0.
6. **No new trusted surface.** The Smoke adversary run under the new
   loop: still refused at the same gates; every admission in the final
   corpus routes through `commitFact`/`commitConcept`.
7. **The floor floors.** With `judgeBudget <` population size, every
   live agent still gets ≥ 1 judgment per generation.

## Sequence

1. W1 + W2: ledger, pricing table, worth-as-fold; `AgentStats` becomes
   a ledger projection.
2. W3: the floor; re-run the economy experiment (tests 1–2, 7).
3. W5: `.concept` proposals, operator/booth agents, verdict events
   (tests 3–5); the Smoke re-run (test 6).
4. Instruments + the matroid derby; then the report.

## Out of scope

Reflective repricing (agents proposing prices — the gate one level up);
compounding operators (slice two); novelty/difficulty terms from the
baseline formula (a second fit, only if the instruments demand it);
booth prompt design.
