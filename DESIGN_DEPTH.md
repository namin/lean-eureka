# Depth: the design (Arc 3)

The prover learns to go deep on purpose, and the economy learns to see
depth. Organized as: what this is, the constraining facts, the
decisions (P1–P7), the acceptance tests, fixed before any code.

**Status: built.** Tiers + attracted credit: `Eureka/Worth.lean`;
escalation (open set, budgeted pass, breadth-before-retries), the deep
ladder, and the induction rung: `Eureka/Concepts.lean` (`escalate`),
`Eureka/Prover.lean` (`tryTacticClosed`, compose depth),
`Eureka/Evolve.lean`. Tests 2–4: `DepthStub.lean` (CI); test 1:
`MatroidDepthRun.lean`, which passed only on its fifth take — the
pre-registered zero flushed out three real defects along the way
(escalation-queue retry starvation; a beta-redex bug in `expandConsts`
that had been blinding every head-indexed rung since slice one; and
proj-headed expansion of structure projections, fixed by the
const-headed-body transparency rule). See REPORT_DEPTH.md. A known
remaining ladder gap, deliberately deferred: composing *through*
iff-shaped bridges on implication goals (the `coindep_def` shape) —
worked around by canonical transparency, a proper rung later.

## What this is

Two coupled ceilings, one arc. The *prover* ceiling: the hunt ladder is
deliberately cheap (refute → refl → grounding → simp → omega → compose
→ tauto/aesop, tight budgets), which is right for sweeps and wrong for
the conjectures that matter — in the grand run, `invented_impls` died
with 33 of 34 conjectures open, and the LLM's best inventions are
unprobeable either way. The *economy* ceiling: an admission pays 1.0
whether refl found it or a composition chain did, so there is no reason
for anyone to attempt anything hard — REPORT_WORTH named this, and the
grand run sharpened it with the booth's fate: killed for unpriced
novelty one generation before its concepts earned four certified
bridges, whose credit went to the prober.

## The facts that constrain the design

- **The opens are already good.** The yield run left 278 implications
  open at a 2000-heartbeat budget; the grand run's `invented_impls`
  left 33. These were *proposed and priced* — the system knows what it
  wants to prove and cannot. Escalation has a ready-made worklist and a
  ready-made regression corpus.
- **Open conjectures are discarded today.** `judge` returns
  `.stillOpen` and the statement survives only in the dedup list; there
  is nothing to escalate *from*. An open set must become state.
- **The rung that proved a fact is already recorded** — every admission
  carries its rung string ("refl", "omega", "composed: …",
  "grounded: X"). Difficulty pricing needs no estimator; the ladder is
  the estimator.
- **Attracted structure pays the wrong agent.** `inventedEdge` credit
  fires only on the fact-judging path; bridges landing via the concept
  path (alias verdicts, re-probe merges) pay the prober only. The
  booth's posthumous ledger is the test case.
- **The matroid pool is blinkered.** `collectKnown [`Matroid]` — but
  the LLM's concepts are built from `Set` operations and `M.closure`;
  the lemmas relating them live in namespaces the prover never loads.

## Decisions

**P1 — Escalation is a budgeted per-generation pass, not a smarter
default.** The cheap ladder stays as-is for every first judgment.
`evolveWith` keeps an **open set** (statement, name, origin, tries);
each generation, after the agent loop, up to `escalationBudget` opens
are re-judged with the deep ladder — priority to statements mentioning
live invented vocabulary, then oldest first; at most 2 escalations per
conjecture, then it rests. A success or refutation exits the open set
through the ordinary gates. *Economics:* the escalated attempt adds
attention to the original proposer, and a success pays them at the
deep tier (P3) — deep truths are net-positive for their proposer;
open-flooding still sinks (each open eventually costs a second
attention with no yield).

**P2 — The deep ladder.** Escalation runs the concept-aware judge with:
ambient (or configured-large) heartbeat budget; the full cheap ladder;
`aesop`/`tauto` uncut; composition depth 3; a widened grounding pool
(domain-configured — for matroids, `Set` and `Matroid.closure`
lemmas join `Matroid.*`); and an **induction rung** for `Nat`-binder
goals (closed-statement tactic of the shape
`intro n; induction n <;> simp_all` with an omega finisher), tried only
here — it is far too expensive for the sweep ladder.

**P3 — Difficulty is the rung, priced in tiers.** `factAdmitted`
carries a tier, classified from the rung that proved it (one
classifier function; plumbing debt acknowledged): **cheap** (refl,
grounding, symm), **standard** (simp, omega, split, permuted, unfold,
chain), **deep** (composed, tauto, aesop), **escalated** (anything
proved by the P1 pass). Prices: cheap and standard stay at 1.0 — the
existing instruments (the ordering test, the derby) recalibrate to
nothing — deep pays 2.0, escalated 3.0. The distortion REPORT_WORTH
named is fixed by paying *more* for depth, not less for ease.

**P4 — Attracted structure pays the inventor.** A new attention-free
event, `conceptAttracted` (price 0.5): whenever a certified bridge
lands on an invented concept — an alias verdict whose *target* is
invented, either side of a re-probe merge — the concept's origin agent
is paid, in addition to (and distinct from) the prober's alias credit.
Posthumous pay is real pay: the ledger doesn't care that the booth is
dead. **No resurrection** in this arc — the concepts live on, which is
what matters; reviving killed agents on late evidence is an open
question, deliberately deferred.

**P5 — Escalation lives in `evolveWith`,** not in an agent: it needs
the open set and the deep config, and its budget must be a *system*
choice, not a worth-ordered one (the whole point is spending on what
the cheap economy undervalued). `EvolveConfig` gains `escalationBudget`
(default 0 — off; existing runs unchanged) and `deepCtx : Option
ProbeCtx` for the deep ladder's configuration.

**P6 — Instruments, fixed in advance.** (i) The regression corpus: the
invented-implications opens from a deterministic grand-run
configuration (no LLM) — escalation must close or refute a nonzero
number of them, with the gate untouched. (ii) The induction rung proves
a pre-registered `Nat` statement the cheap ladder leaves open.
(iii) The booth-vindication replay: a concept whose origin agent is
dead attracts a bridge; the origin's ledger value rises. (iv) At equal
volume, a deep-truth proposer out-earns a cheap-truth proposer.
(v) The full existing suite — ordering, derby, economy separation —
passes unchanged (cheap/standard at 1.0 is what makes this a theorem
rather than a hope).

**P7 — Out of scope.** LLM proof repair as an escalation rung (the
baseline's `ProofRepairWorker` pattern — natural slice two of this
arc); agent resurrection; reflective repricing (still the
gate-one-level-up axis); any change to the birth gate or probe
verdicts.

## Acceptance tests (written before building)

1. **Escalation closes real opens** (`MatroidDepthRun.lean`,
   deterministic): from a no-LLM grand-run configuration's open set,
   the escalation pass admits or certifiably refutes ≥ 1 conjecture the
   cheap ladder left open; every admission through `commitFact`; audit
   clean.
2. **The induction rung works** (`DepthStub.lean`, CI): a
   pre-registered `Nat` statement — open on the cheap ladder, proved
   under escalation by the induction rung, admitted through the gate.
3. **Vindication pays** (`DepthStub.lean`): the grand-run scenario in
   miniature — inventor agent killed, its concept later attracts a
   certified bridge, `conceptAttracted` raises the dead agent's ledger
   value; the prober's own credit is unchanged.
4. **Depth out-earns ease at equal volume** (`DepthStub.lean`): two
   agents, equal admission counts, one all-cheap and one all-deep; the
   deep proposer's worth is strictly higher.
5. **No regression** (existing suite): WorthStub's ordering, the derby,
   the economy separation, and the Smoke/audit adversaries all pass
   with escalation off *and* with `escalationBudget > 0` — the gate
   surface is unchanged by construction.

## Sequence

1. P4: `conceptAttracted` + credit wiring (+ test 3).
2. P3: tiers + classifier (+ test 4; re-run the existing suite).
3. P1/P2/P5: the open set, the escalation pass, the deep ladder, the
   induction rung (+ tests 1–2, 5).
4. `MatroidDepthRun` + the report: how many of the grand run's open
   class fall to escalation, and what the tier distribution of a
   population's admissions looks like once depth pays.
