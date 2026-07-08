# REPORT: NL heuristics — the representation derby (lean-eureka)

Built and run to `DESIGN_HEURISTICS_NL.md`: heuristics whose body is an
English string, fired by the trusted `nlAgent` combinator through one
metered LLM call per firing, in one population with the code rungs —
same gates, same pricing. Every number below that says "admitted" is a
kernel-gated fact; the NL rung has no admission path of its own (N1,
W4). Model: `us.anthropic.claude-sonnet-5` via Bedrock; 39 LLM calls
total; full transcript `transcripts/nl-derby.jsonl` (R1).

## Setup

`NLRun.lean`, Nat domain, 6 generations, judge budget 40, NL budget 6
calls/generation, exploration floor on, no domain refuter, escalation
off. Population at seed: the six hand-written template agents
(`identityH` … `mixerH`), `specializerH` (births explorer/probe *code*
to depth 2), `llmOracleAgent` (births LLM-written *code* through the
rule gate; deliberately unmetered — the kept asymmetry), and the NL
rung: verbatim ports of the baseline's three conjecture-kind templates
(`nl_algebraic_identities`, `nl_boundary_cases`, `nl_analogy_transfer`)
plus `nlOracleAgent` (births LLM-written *English* through the NL
gate, metered).

**Run notes.** The first live attempt died in generation 4:
`(deterministic) timeout at elaborator` — the command's cumulative
200k-heartbeat budget, exhausted not by judgments (each gets a fresh
budget) but by loop overhead: reply parsing, the growing defeq-dedup
scan, printing. Fix: `judge` now pins its per-judgment budget
(`judgeHeartbeats := 200000`, `Eureka/Loop.lean`) so drivers can raise
the command ceiling without silently deepening the prover;
`NLRun.lean` raises the ceiling for overhead only. `BoothStub`'s
exact-corpus assertion (and every other CI stub) passes unchanged —
same prover, same outcomes. The aborted attempt's transcript is kept
(`transcripts/nl-derby-attempt1.jsonl`, 19 calls).

## The numbers

Final corpus: **140 facts, all kernel-gated**. No agent was killed in
6 generations. By representation:

| rung | agents | admitted | refuted | open | LLM calls |
|---|---|---|---|---|---|
| hand-written code | identity, comm, idem, assoc, distrib, mixer | 23 | 35 | 0 | 0 |
| born code (specializer chain) | 7 explorers + 7 probes | 8 | 11 | 1 | 0 |
| born code (LLM-written) | llmborn_23/41/68/84/100/119 | 4 | 30 | 2 | 6 |
| NL seeds (baseline ports) | algebraic_identities, boundary_cases, analogy_transfer | 75 | 3 | 6 | 18 |
| NL born (oracle children) | nlborn_23/58 (fired), _84/_100/_119 (starved) | 30 | 9 | 8 | 15 |

The NL rung produced **105 of 140 admissions (75%)** on 33 metered
calls — 3.2 admissions per call. Decided-precision
(admitted/(admitted+refuted)): NL seeds 96%, NL born 77%, hand-written
code 40%, specializer chain 42%, **LLM-written code 12%** (llmborn_23
alone: 0 admitted, 13 refuted). Same model, same corpus view, two
authoring targets: the LLM writing *English* heuristics yielded 30/9
through its children; the LLM writing *Lean metaprogram* heuristics
yielded 4/30.

Final worths (excerpt): specializer, both oracles, explore_max/min at
1.00 (child credit / small attention); nl_analogy_transfer **0.84**;
assoc 0.80; comm 0.77; nl_algebraic_identities 0.73; nl_boundary_cases
0.63; nlborn_58 0.62; nlborn_23 0.57; identity 0.36; llmborn_23 0.26.

## Reach — the N6 headline number

**27 NL admissions mention `Nat.lcm`, an operation no code rung can
state**: `opPool` is add/mul/sub/pow/max/min/gcd, so the code
representations are confined to equations over those seven heads. The
analogy-transfer seed introduced lcm as gcd's analogue and the rung
built its theory across generations 3–6, including:

- `∀ a b, a.gcd b * a.lcm b = a * b` (grounded)
- `lcm` commutativity, associativity, idempotence, absorption by 0/1
- `∀ a b c, a * b.lcm c = (a * b).lcm (a * c)`
- `∀ a b, min a b + max a b = a + b`, `∀ n, n.gcd (n + 1) = 1`

Beyond vocabulary: 13 NL admissions use divisibility (`∣`) and 3 use
implications (`a ∣ b → a.lcm b = b`) — statement *shapes* outside
every code template, which are equation-only. Zero NL proposals were
defeq-merged into code-agent statements (0 dups on all five fired NL
agents); overlap with the code rungs occurred only as free verbatim
repeats. The N6 reach criterion is met: the NL rung admitted families
the code rungs never attempted and cannot express.

The port that earned most — analogy_transfer, 34 admitted / 0 refuted
— is the one whose example list is entirely off-domain (Group↔Ring,
Nat↔Int, List↔Multiset). The heuristic's *idea* transferred; its
examples did not need to.

## The tautology farm — the other headline

**22 of the 105 NL admissions (21%) are farmed trivialities**: 20 of
the shape `P ∨ True` and 2 of the shape `x = x` (e.g.
`a.lcm b - a = a.lcm b - a`). All kernel-true — the gate is sound and
was never at risk — and all worthless, each paid the full admission
price (1.0).

The spread is visible generation by generation: nlborn_23 invented the
move in generation 3 (3 admissions via `simp`), and it diffused
through the shared prompt medium — the corpus listing every NL agent
sees — to every NL agent by generation 6 (g3: 3, g4: 3, g5: 6, g6: 8,
plus the two refl facts). By generation 6 even the *code* oracle's
prompt reply describes the corpus' "`∨ True` weak forms" (transcript
call 32). Excluding the farm, NL decided-precision is still 87%
(83/95).

This is the NL rung's alias-farming analogue, surfaced in one run:
pay-certainty pricing pays trivial certainty, and `admittedDeep`
pricing (P3: "ease does not pay less") means a `simp`-trivial
tautology earns exactly what a hard composition earns.

## Metering, births, starvation

- 39 calls: 33 metered (`.llmCalled` attention) + 6 unmetered
  (`llm_oracle`, the kept asymmetry). Both oracles finished at worth
  1.00 on child credit — but the code oracle's children were 12%
  precise on zero metered cost, while the NL oracle paid 6 attentions
  for children at 77%.
- 5 NL births passed the gate; 0 gate refusals; 1 silent drop: the
  generation-3 oracle proposal was named `nlborn_58` by the
  corpus-size naming scheme (shared with `llmOracleAgent`), collided
  with the generation-2 child, and was skipped as already-born. A
  naming scheme that can silently discard a distinct proposal is a
  known wart from this run.
- Worth-ordered NL scarcity bit exactly as designed: with 7–8
  `llmPerFire` agents competing for 6 calls/generation by generations
  5–6, the late borns (nlborn_84, _100, _119) at cold-start worth 0.50
  never outbid the earning seeds and **fired zero times**. The
  exploration floor covers the judge budget only, not the NL budget —
  a born NL heuristic can die unheard under sustained scarcity.

## Interpretation (separate from the facts above)

1. **Reach is real and it is vocabulary escape.** The code rungs are
   bounded by their operation pool and equation templates; the NL rung
   walked out of both (lcm, `∣`, implications) and 75% of the final
   corpus came from it. The representation ladder's top rung earns its
   place on expressiveness, not just volume.
2. **The farm is the derby's pricing demand.** As the economy
   experiment demanded refutation pricing and the yield table demanded
   novel-pays-zero, this run demands a response to trivial certainty:
   a proposal-time triviality screen (the concepts' ⊤/⊥ move applied
   to facts — refl/`∨ True` shapes verdicted degenerate), or a price
   fit where cheap-tier admissions decay. That collides with P3's
   "ease does not pay less" ruling — a deliberate conflict to resolve
   by instrument, not here (W1: prices are data).
3. **Metering the code oracle is now supported by data.** The
   asymmetry was kept pending evidence; the evidence is 6 free calls
   producing 12%-precision children whose parent sits at 1.00.
4. **The prompt is a shared medium.** Corpus-in-prompt is how the NL
   rung learns, and also how junk styles propagate agent-to-agent —
   an imitation channel the code rungs don't have, observable line by
   line in the transcript.
5. **An NL exploration floor is worth ruling on** (one guaranteed call
   per live NL agent per generation, like W3), or late borns under
   scarcity are structurally silent.

## Reproduction

```
lake env lean NLStub.lean    # acceptance tests 1–6 (CI, canned transport)
lake env lean NLRun.lean     # the live derby (Bedrock; ~39 calls)
transcripts/nl-derby.jsonl          # this run, complete (39 calls)
transcripts/nl-derby-attempt1.jsonl # attempt 1 (gen-4 heartbeat death, pre-fix)
```
