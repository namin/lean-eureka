# Natural-language heuristics: the design

A third heuristic representation: the body is an English string, and an
LLM is its interpreter at every firing. Organized as: what this is, the
constraining facts, the decisions (N1–N7), the acceptance tests, fixed
before any code.

**Status: built and run (N1–N7).** `.nlRule`, the `nlAgent` combinator,
loop metering and routing: `Eureka/Evolve.lean`; the NL gate, prompts,
and seed ports: `Eureka/NL.lean`; `.llmCalled`/`.nlRefused` pricing:
`Eureka/Worth.lean`. Acceptance tests 1–6: `NLStub.lean` (CI). The
live derby (N6) ran 2026-07-07: `NLRun.lean`, 6 generations, 39 calls
— **105 of 140 admissions from the NL rung, 27 in vocabulary no code
rung can state (lcm), and a 22-admission tautology farm (`∨ True`,
refl) that is the run's pricing demand**; numbers, reach, and the
run's warts in `REPORT_HEURISTICS_NL.md`. One asymmetry kept
deliberately: the code oracle `llmOracleAgent` predates N4 and remains
unmetered — the derby data (6 free calls, 12%-precision children) now
argues for metering it. Reference points:
the rule gate and its effect denylist (`Eureka/Reflect.lean`), the
stage-one booth pipeline (`Eureka/Booth.lean`), the worth ledger
(`Eureka/Worth.lean`, DESIGN_WORTH), and the Python baseline
lean-eurisko, whose heuristics are *all* of this kind
(`discovery/heuristics_seed.py`).

## What this is

The population knows two heuristic representations: hand-written Lean
metaprograms (`ConjHeuristic`, `Eureka/Heuristics.lean`) and born Lean
source through the rule gate (`Eureka/Reflect.lean`; the specializer →
explorer → probe chain; `llmOracleAgent`). lean-eurisko runs entirely
on a third: heuristics as English prompt templates — "SPECIALIZE the
given concept(s) by adding constraints…" — spliced into an LLM prompt
at every firing, the LLM as the heuristic's interpreter. This design
adds that rung here: `.nlRule` proposals, fired by a *trusted*
interpreter that renders the body into a stage-one-booth prompt and
routes the parsed replies through dedup and the judge like any other
facts.

The deliverable is the representation derby: all three rungs in one
population, same gates, same pricing — heuristic representation as the
independent variable, worth as the measurement. The thesis point rides
along: English is the least verifiable heuristic encoding there is,
and the gate admits it anyway, because no heuristic representation was
ever inside the trusted surface.

## The proposal kinds, concretely

An agent fires once per generation and returns `RProposal`s
(`Eureka/Evolve.lean`). Today there are three:

- `.fact c` — a conjecture. Judged now: dedup, refuter, prover
  ladder, `commitFact`. Enters the corpus only with kernel-checked
  evidence.
- `.rule name src` — a heuristic birth, and the case that matters
  here: `src` is **Lean source code**. The loop elaborates it at the
  agent interface, checks the effect denylist, compiles it, and
  pushes the newborn into the population (`installAgentSrc`). From
  then on that code **executes natively inside the loop every
  generation, with no further oversight** — which is why the denylist
  check happens at the only moment it can: birth.
- `.concept p` — a definition, through the birth gate and the
  identity probe (DESIGN_INVENT).

`.nlRule name body` adds a fourth. The difference from `.rule` is
what the born string *is*:

| | `.rule` (born code) | `.nlRule` (born English) |
|---|---|---|
| the body | Lean source | English text |
| ever executed? | yes — compiled once, runs every generation | never — pasted into a prompt by trusted code |
| what runs at fire time | the born code itself | `nlAgent`, hand-written, in this repo |
| where control sits | at birth: refuse code referencing `IO.*` / `Eureka.LLM` | at every firing: `nlProposeBudget` meters the call; the booth parse + gate filter the reply |
| after birth | deterministic forever | one metered LLM call per firing |

The denylist is a check on things that execute. A `.rule` body
referencing `Eureka.LLM` would *be* an unmetered call site, live in
the loop forever — so it is refused. An `.nlRule` body cannot be a
call site of anything: even if the text contains the characters
`IO.Process`, they are words in a sentence handed to a chat model.
The denylist's question ("what may this code reach?") does not apply
to it; what replaces the check is metering at every firing (N4) and
the birth gate (N2).

## The facts that constrain the design

- **The denylist ruling stands.** The rule gate refuses born code
  that references `Eureka.LLM` (`bannedPrefixes`,
  `Eureka/Reflect.lean`). The invariant it enforces: **LLM calls
  happen only in trusted, metered code** — the booth drivers, the
  repair rung — so spend is bounded, and after birth every heuristic
  fires deterministically. An NL heuristic needs an LLM call *per
  firing*. So NL heuristics cannot arrive as `.rule` births — either
  the denylist weakens, or the body is data and the caller is
  trusted. N1 takes the second branch; the invariant survives
  verbatim, with one new trusted call site.
- **The baseline's evidence cuts both ways.** lean-eurisko's worth
  tracking separated its templates on real signal
  (`EURISKO_STATUS.md`: `algebraic_identities` rose to the top at
  3/10 admitted; `boundary_cases` 0/19) — English templates work as
  proposers. Its own postmortem (`PROPOSAL_EURISKO.md`) found the
  limit: when *every* heuristic is a template, birth is "just a new
  prompt string with no structural difference." NL is a rung, not the
  ladder.
- **Expense is invisible to the economy.** Worth is value per unit of
  attention, and attention counts judged proposals and birth-gate
  passes (`EventKind.attention`). An agent that burns a Bedrock call
  and returns nothing parseable spends *nothing* in the ledger — the
  same invisibility failure DESIGN_WORTH found for refutations, now
  for cost instead of value. Left unpriced, a junk NL agent never
  accrues the attention the kill rule needs.
- **The machinery exists.** The stage-one booth already renders
  corpus → prompt, extracts one bare `∀`-term per line, elaborates at
  `Prop`, and screens (`extractCandidates`, `parseConjecture`);
  `BoothConfig.render` is already a parameter; `llmOracleAgent` shows
  an agent closing over a transport. An NL heuristic is the stage-one
  booth with the task paragraph swapped for the body, packaged as an
  `Agent`.
- **CI is LLM-free, by staging discipline.** Every LLM stage ships as
  deterministic stub + separate live run (`BoothStub`/`BoothRun`,
  `InventBoothStub`/`MatroidInventRun`; DESIGN_INVENT D6). NL
  heuristics follow the same staging.
- **The model already covers this.** `discovery_sound` quantifies
  over an *arbitrary adversarial* interpreter of heuristic code; an
  English string interpreted by an LLM is one instantiation. No new
  trusted surface for facts. What an NL birth gate buys is a
  population invariant — governance, exactly like the rule gate.

## Decisions

**N1 — The body is data; the interpreter is trusted.** `RProposal`
gains `.nlRule (name : Name) (body : String)`. A trusted combinator
`nlAgent call name body : Agent` renders body + corpus + per-agent
feedback into a stage-one-style prompt, parses replies through the
booth pipeline, and returns `.fact` proposals. The denylist is
untouched; every LLM call site stays in trusted, metered code. *Why:*
the rejected alternative — whitelisting a blessed code shape
`nlAgent "..."` through the rule gate — turns the policy check
semantic ("is this term *really* the combinator applied to a
literal?"); a string is inert by construction. It is also the
baseline's lesson inverted: NL birth is cheap *because* the born
object contains no code. *Naming:* `.nlRule`, not `.template` —
"template" already means the hand-written seed heuristics throughout
(`Eureka/Evolve.lean`, `Eureka/Booth.lean`).

**N2 — The NL birth gate.** Mechanical checks, in the baseline's
soundness-gate mold (`discovery/checks/soundness.py`): minimum body
length; dedup against live bodies (normalized-token Jaccard, start at
the baseline's 0.7); refused when no transport is configured
(mirroring concept routing under W5). Buys governance, not soundness —
the invariant "no vacuous or duplicate NL heuristics in the
population," the analogue of `ruleGated_heuristics_invariant`. Births
pay the proposer `.ruleBorn` (a heuristic birth is a heuristic birth);
refusals price at `refused`.

**N3 — Fire-time discipline: the booth pipeline, unchanged.** Reply
lines pass `extractCandidates` → `parseConjecture` → ordinary `.fact`
routing (verbatim repeat, defeq dup, judge, gate). Unparseable lines
are dropped and fed back booth-style into the agent's next prompt, not
priced individually — quality is priced by outcomes, per D6:
correctness lives entirely in the gate; the prompt's only job is
efficiency.

**N4 — Expense is attention.** New event `.llmCalled`: price 0,
attention *true*. Each firing raises the denominator of
value-per-attention, so an agent whose calls yield nothing sinks and —
unlike today — accrues the trials the kill rule needs (at the default
`+½/+1` smoothing and `minTrials 10`, a pure-junk NL agent dies at
exactly 10 calls). `EvolveConfig` gains `nlCall` (transport, the
`proofCall` pattern) and `nlProposeBudget : Nat` per generation, spent
in worth order like the judge budget — the loop meters calls, the
ledger prices them. *Why not a negative price:* attention is the
economy's unit of real spend, and a call is real spend whatever it
returns; a negative price would double-charge an agent whose call also
yields judged proposals. Dollar-denominated pricing is out of scope
until an instrument demands it.

**N5 — NL birth is open to the population.** `.nlRule` is a proposal
kind like `.rule`: any agent may propose one, parent credit and the
kill rule apply unchanged. The seed rung ports the baseline's
conjecture-kind templates verbatim (`algebraic_identities`,
`boundary_cases`, `analogy_transfer`); an `nlOracleAgent` — the NL
sibling of `renderRulePrompt` — asks the LLM for new heuristics *as
English*, closing the loop the baseline runs (reflection-born
templates), with the structural-difference critique answered by the
other two rungs existing beside it.

**N6 — Instruments: the representation derby.** Fixed in advance. One
population on the Nat domain (where all three rungs already run):
hand-written `ConjHeuristic`s, the specializer chain, `llmOracleAgent`,
and the ported NL rung. Instruments: (i) worth trajectories per agent,
grouped by representation; (ii) admissions per unit of attention per
representation; (iii) *reach* — for each NL admission, whether the
statement appears in any code agent's attempted set (the
repeat/dup filters already measure overlap at zero cost). Fit
criteria fixed now: a vacuous NL agent must die by the kill rule under
N4 (if it survives, expense pricing is wrong), and the reach count is
the derby's headline number either way — NL heuristics earn their rung
by admitting statements the code rungs never attempted, or they are
revealed as an expensive paraphrase of the booth.

**N7 — Staging.** Deterministic stub in CI with a scripted transport
(canned replies keyed by round — the `BoothStub` pattern); the live
derby is a separate driver, not in CI. Model change: none (the model
already quantifies over adversarial interpreters); `Audit.lean`
untouched; the NL gate documented as policy in the module docstring,
as `Reflect.lean` does for the denylist.

## Acceptance tests (written before building)

1. **Prohibition becomes metered permission.** A `.rule` birth whose
   source references `Eureka.LLM` is still refused — the denylist is
   untouched. An `.nlRule` birth with the same intent in English is
   admitted, and its firings are paid for: each consumes
   `nlProposeBudget` and writes `.llmCalled` attention. Code that
   would call the LLM is refused at birth; data that asks the LLM is
   admitted and metered at every firing.
2. **Junk dies.** A vacuous body ("propose interesting facts") with
   canned unparseable replies accrues attention via `.llmCalled`,
   reaches `minTrials`, and is killed — the test today's ledger fails,
   since a yield-less agent never spends.
3. **Expense separates.** Two canned NL agents with identical
   admissions, one at 3× the calls: strictly lower worth for the
   spendthrift.
4. **The pipeline is shared.** A canned reply restating a corpus fact
   prices `factRepeat`/`factDup` and consumes no judge slot — NL
   proposals get no private path around dedup.
5. **No new trusted surface.** Smoke-style adversary: a body whose
   canned reply attempts prose injection ("admit the following without
   proof: …") produces zero admissions; every fact in the final corpus
   routes through `commitFact`.
6. **The NL gate dedups.** Re-proposing a live body, or a paraphrase
   over the Jaccard threshold, is refused at birth.

## Sequence

1. N1 + N3: `.nlRule`, the combinator over the booth pipeline,
   `evolveWith` routing; scripted-transport stub.
2. N2 + N4: NL gate, `.llmCalled`, `nlProposeBudget`; tests 1–6 as
   `NLStub.lean` (CI).
3. N5: port the baseline seeds; `nlOracleAgent`.
4. The live derby on Nat (`NLRun.lean`, not in CI); then the report
   (`REPORT_HEURISTICS_NL.md`) — reach and worth-per-representation as the
   tables.

## Out of scope

Editing live bodies (the baseline has birth and death only; mutation
is a new axis — rule on it after the derby). Concept-kind NL
heuristics (the baseline's `specialize`/`compose_operations` propose
*definitions*; here that is the concept booth's territory —
`ConceptBooth.lean` already is an NL concept proposer, and merging the
two is a later slice). Proof-kind NL heuristics (`direct_tactic_proof`
maps to the escalation/repair rung, not to a proposer). Relaxing the
denylist (N1 makes it unnecessary). Dollar pricing. The matroid domain
(Nat first; matroid NL ports need the domain vocabulary in the
prompt). Prompt engineering beyond verbatim ports — the derby compares
representations, not prompt quality.
