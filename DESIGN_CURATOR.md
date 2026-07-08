# The curator: the design

The LLM moves from proposer to Lenat's seat: curating a symbolic
mutation stream — attention, mutation steering, triage, labels — through
the schedule-only seam the model already proved harmless (W4). Organized
as: what this is, the constraining facts, the decisions (L1–L8), the
acceptance tests, fixed before any code.

**Status: design only.** Nothing built. Reference points: the
schedule-invariance ruling (DESIGN_WORTH W4, `discovery_sound`), the
worth ledger (`Eureka/Worth.lean`), the rule gate and the specializer
chain (`Eureka/Evolve.lean`), the derby's findings
(`REPORT_HEURISTICS_NL.md`), and eurisclo — the lineage's symbolic
mutation vocabulary.

## What this is

EURISKO was never autonomous. The mutations were symbolic, and Lenat
was the nightly curator — killing degenerate concepts, nudging worth,
choosing what to mutate next, naming and narrating what came out; the
results were "Lenat + EURISKO." The curator was always the
unmechanizable component. This design puts an LLM in that seat, inside
the verified loop, restricted by type to the one channel that provably
cannot corrupt the corpus: attention.

This completes the LLM's seat map, and reorders it. Seat one: proposer
of facts (the booth). Seat two: author of heuristics — as Lean code
(`Reflect`) or English (`DESIGN_HEURISTICS_NL`). Seat three: curator
(this design). Seats one and two are opt-in arms of the representation
derby; the **standing configuration becomes symbolic proposers +
curator** — the LLM makes sense of what a symbolic engine generates,
rather than generating.

The derby motivates the demotion of the authoring seats: as author,
the LLM was weak (Lean-authoring, 12% decided-precision children) or
corrupting (English-authoring: 75% of the corpus, but 21% of it a
tautology farm that spread by prompt imitation). Curation is the seat
where sense-making pays and where the failure mode has no channel:
player and referee separate, and the symbolic proposers cannot author
`∨ True` — the exploit is not in their generative space.

## The facts that constrain the design

- **The seam is already proved.** `discovery_sound` quantifies over
  adversarial interpreters and schedules; worth selects what gets
  judged, never what gets admitted (W4). A curator whose entire action
  space is attention adds no trusted surface for truth — it can waste
  budget, never widen admission. Everything in this design must stay
  inside that seam.
- **The value layer is unverified, and it got gamed** (the derby: 22
  farmed admissions, invented generation 3, diffused to every NL agent
  by generation 6). A curator is a value-layer referee — but a
  *fallible* one. Its judgments must be ledger data: bounded,
  decaying, auditable, and calibratable against later ground truth —
  never silent state.
- **Kill decisions starve provable queues.** Three recorded
  occurrences of the economics-vs-completeness tension, plus the
  derby's starved late-borns. Curator taste must not get a kill
  switch; the mechanical rule is the floor.
- **The mutation machinery half-exists.** The specializer chain births
  heuristic code from corpus data; the concept operators (dualize,
  singleton-lift, compounding) mutate the concept pool. Missing is
  EURISKO's general move — operators over existing heuristic *source*
  (the eurisclo vocabulary): that is what gives the curator a real
  stream to tend.
- **Curator calls are LLM calls.** Metering and pricing exist
  (`.llmCalled`, N4); the escalation pass is the precedent for a
  *system* budget deliberately outside worth ordering. Transcripts are
  mandatory (R1).
- **Strict parsing is the house discipline.** The concept booth's
  fixed line format, the NL booth's bare-`∀` lines: the curator's
  action grammar must be closed and strictly parsed; malformed output
  drops harmlessly and is logged.

## Decisions

**L1 — The curator is schedule-only, by type.** One call per
generation; the reply is parsed against a closed action menu:
`boost a`, `damp a` (bounded, decaying attention nudges), `escalate c`
(spend escalation slots on named opens), `mutate a op` (apply symbolic
operator `op` to agent `a` — L4), `label x text` (display-layer only:
concept labels, run narration). No action constructs a statement, a
heuristic, a concept, a definition, or a price. *Why:* every action
lands inside W4's seam; the adversarial-curator worst case is wasted
attention, which the economy already prices. The rejected alternative
— curator-authored proposals — is the proposer seat, already built,
already optional, and already measured.

**L2 — Curator influence is a ledger event, not hidden state.**
`curatorBoost`/`curatorDamp` events with fixed magnitude, folded into
worth as a capped, per-generation-decaying term (prices are data, W1):
total curator-attributable worth shift per agent bounded by a cap that
cannot cross the kill threshold's distance on its own. *Why:*
trajectories stay a projection of the ledger; curator influence is
visible in the same instrument as everything else, and calibration
(L7) needs the events.

**L3 — The kill rule is untouched.** Kills still require `attention ≥
minTrials ∧ worth < killThreshold`; curator taste reaches death only
through the bounded priced events of L2, and a boost can delay a kill
by at most the cap's worth. There is no kill action and no spare
action. *Why:* the starvation findings — taste must not silently
delete provable queues; acceleration and delay are priced and bounded,
decree is impossible.

**L4 — The mutation stream is symbolic; the curator only chooses.**
A fixed operator set over heuristic source — `substOp` (swap one
operation for another in a template's family), `restrictPool` (narrow
a heuristic's operation pool to where it has earned), `crossover`
(graft one heuristic's law schema onto another's operation pool) —
applied by a mechanical mutator to the *source text* the system
already generates (`explorerSourceFor` pattern), with every mutant
entering as an ordinary `.rule` birth through the rule gate, parent
credit intact. The curator's `mutate` action selects target and
operator; it never writes the mutant. *Why:* EURISKO's generativity
without the authoring attack surface — the derby showed authoring is
where the LLM is weak or corrupting, and choosing is where judgment
lives. Symbolic mutants also cannot express the farm: the operators
are equation-schema-shaped.

**L5 — Escalation steering.** The curator's `escalate` actions
nominate opens for the existing escalation pass, consuming the
existing `escalationBudget` (a system budget, not worth-ordered —
P1/P5 precedent). Un-nominated slots fall back to today's ordering.
*Why:* triage was half of Lenat's job; the machinery exists and is
already schedule-only.

**L6 — Interestingness flags, priced and bounded.** The curator may
flag an admitted fact as trivial-in-spirit: a `curatorFlagged` event,
small negative value to the origin agent, same cap-and-decay regime as
L2. Flags never touch the corpus — facts are append-only, and only
certificates tombstone (D3). *Why:* the value-layer referee the farm
demanded, with fallibility priced in: a wrong flag costs bounded
worth, is visible in the ledger, and is scored by L7. (The
*certified* triviality screen — alias-of-`True` probing — is separate,
mechanical, and complementary; it needs no curator and is ruled
elsewhere.)

**L7 — Calibration instruments, fixed in advance.** (i) The ablation:
symbolic-only vs. symbolic + curator, same seeds and budgets —
admissions per judge slot, depth-2 births reached, opens resolved.
(ii) The planted farm: with the NL arm on and a canned farm agent
seeded, curator-flag damping must drive it under the kill threshold
strictly faster than the no-curator control (which the derby showed
pays it). (iii) Calibration proper: curator boosts and flags scored
against later ground truth — grounding-use of boosted agents' facts,
non-use of flagged ones (sharpens to usage royalties when that pricing
lands). (iv) Taste-drift: lineage diversity of curator-selected
mutants vs. round-robin mutation — the Goodhart watch on selection
pressure. If curation does not beat the ablation, the seat is
decoration; the criterion is decided now.

**L8 — Metering and staging.** `curatorCall` transport +
`curatorBudget` (calls per generation, default 1) in `EvolveConfig`;
every call transcripted (R1); prompt = agenda with worths, last
generation's ledger events rendered, sampled outcomes, and the action
grammar. Malformed lines drop and are logged, booth-style.
Deterministic `CuratorStub.lean` with canned replies in CI; the live
run is a separate driver. Model change: none — the curator is an
instantiation of the adversarial scheduler `discovery_sound` already
quantifies over.

## Acceptance tests (written before building)

1. **The adversarial curator is harmless.** Canned worst-case curation
   (boost junk, damp every honest agent, flag everything, mutate
   constantly) over a fixed symbolic run: every corpus fact still
   routes through `commitFact`, the axiom audit stays clean, and the
   corpus differs from the control only in *which* gate-admitted facts
   arrived — Smoke's adversary, promoted to the scheduler.
2. **Bounds bind.** An agent with zero certified value, boosted every
   generation, still dies by the mechanical rule; a productive agent,
   damped every generation, still survives the floor. The cap and
   decay are asserted exactly.
3. **The stream flows.** A `mutate comm substOp` action births a
   rule-gate-passed mutant whose proposals are the swapped family,
   with parent credit and lineage visible in the ledger.
4. **The planted farm dies faster.** Instrument (ii) as a two-run
   stub: kill generation with curator < kill generation without.
5. **Garbage curation is inert.** A canned reply of prose, unknown
   actions, and malformed lines: run completes, actions dropped and
   logged, ledger untouched by the dropped lines.
6. **Determinism.** `CuratorStub.lean` is bit-stable in CI: canned
   transport, no credentials.

## Sequence

1. L4 mechanical mutators + test 3 (no LLM anywhere — the mutation
   stream has value curator-less, via round-robin).
2. L1–L3: action grammar, events, prices, caps; `CuratorStub.lean`
   (tests 1, 2, 5, 6).
3. L5–L6; the planted-farm stub (test 4).
4. The live ablation on Nat, then matroid (refuter on); L7's four
   instruments; `REPORT_CURATOR.md`.

## Out of scope

Curator-proposed prices or screens (reflective repricing — the
gate-one-level-up axis stays deferred; L2/L6's bounded events are
deliberately weaker than price edits). The certified triviality screen
(alias-of-`True` probing — mechanical, complementary, its own small
design). Usage-royalty pricing (its own design; L7-iii wants it and
will say so). Multi-curator panels, curator memory across runs,
curator-authored anything. Prompt engineering of the curator beyond
the fixed grammar.
