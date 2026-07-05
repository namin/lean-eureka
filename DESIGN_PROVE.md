# Proving: the design (Arc 4)

The hunt learns to search. Two slices — the LLM repair rung (the
measured control) and the tactic-state stepper (the wager) — plus
premise retrieval feeding both. Organized as: what this is, the
constraining facts, the decisions (V1–V7), the acceptance tests, fixed
before any code.

**Status: built and measured.** Retrieval + repair + stepper:
`Eureka/Prover.lean`, `Eureka/Prove.lean`, wired into `evolve` behind
`proofCall`/`llmProofBudget` (off by default). Tests 1–3, 5:
`ProveStub.lean` (CI). Tests 4 and 6: `MatroidProveRun.lean` — the
control **passed** with the system's first LLM-proved fact
(`IsCircuit X → MIsCyclic M X`, closed on the repair round), and the
wager came back **null on this sample** (the stepper added no closures;
the interaction-beats-repair hypothesis is no longer default-true).
See REPORT_PROVE.md.

## What this is

Everything the system proves today comes from a fixed ladder of
one-shot attempts. Arc 3 made the ladder deeper and priced its depth;
what no slice has yet built is *search* — and the conjectures that
matter (the LLM's existential-body inventions, the residual open
classes) are beyond any fixed ladder. The question this arc puts to an
instrument: does proof search need to be *interactive* (seeing goal
states), or does one-shot generation with error repair suffice?

The baseline already answered half of this the hard way. Its
`ProofWorker` → `ProofRepairWorker` pipeline is exactly one-shot +
repair, and its measured ceiling is documented: the Whitney target
died in 100+ targeted attempts, proofs stayed "wide but shallow," and
REDESIGN.md names tactic-state interaction as the missing capability —
named, never built, because the baseline lived outside the prover.
lean-eureka lives *inside* `MetaM`: goal states are data, no
subprocess, no REPL protocol. Interaction is the one structural
advantage over the baseline not yet spent.

## The facts that constrain the design

- **The one-shot ceiling is measured** (baseline REPORT_MATROID,
  REDESIGN): repair helps (their proof rate rose to ~38% after the
  repair loop landed) and then plateaus. Building repair in-process is
  the control arm, not the hypothesis.
- **The regression corpus exists**: the deterministic matroid residual
  opens (the `dual_IsRkFinite` and `elem_dual_IsBase` families), the
  grand run's `invented_impls` opens, and the LLM's existential-body
  concepts, unprobeable by every symbolic rung.
- **The seams exist**: `escalate` is where expensive proving already
  lives; tiers price it; attention charges it; canned transports keep
  CI deterministic (every booth's pattern).
- **The trust story must not move**: whatever any search finds passes
  `commitFact` — screen, kernel, axiom audit. Notably the audit
  already refuses `native_decide`-style shortcuts (its axiom is not in
  `allowedAxioms`), so LLM scripts need no text screening to keep the
  corpus sound; refusal remains safe.

## Decisions

**V1 — Slice one: the repair rung, built as the control.** A new
escalation rung, after the symbolic deep ladder (symbolic first — it
is free): prompt = the statement, the pretty-printed goal, and
retrieved premises (V2); the model returns one `by`-script; the script
is elaborated against the closed statement (`tryTacticClosed`
machinery); on failure, **one** repair round carrying the error text;
cap two LLM calls per conjecture. Success commits through the gate at
the escalated tier, rung note `escalated: llm-repair`. The transport
is a parameter on the escalation config (`none` = rung off — every
existing run and stub is unchanged by construction).

**V2 — Premise retrieval, symbol-overlap first.** Rank the grounding
pool by overlap between the goal's constants and each lemma's
constants; top-k (≈12) pretty-printed into the prompt. No embeddings
in this arc (recorded as the upgrade path); the same retrieval feeds
both slices. ~30 lines, shared.

**V3 — Slice two: the stepper.** Proof search over tactic states:
state = the open goals of an in-progress proof (fresh metavariable,
tactics applied via the elaborator); moves = (a) a curated set of
cheap single tactics (intro, constructor, cases on hypotheses, simp,
omega, the targeted domain simp), (b) the LLM as a *move generator* —
it sees the current goal rendered, with retrieved premises, and
returns one tactic line, not a proof. Failing or ill-formed moves are
discarded; search is best-first on (goals remaining, depth), bounded
by a node budget. Success extracts the assembled proof term, which
goes to the gate like any other. The wager, stated for the instrument:
seeing the goal after each step closes conjectures that one-shot
generation with error text cannot.

**V4 — Economics.** LLM proof calls are metered per generation
(`llmProofBudget` — they cost money, not heartbeats) and charged as
attention to the conjecture's proposer, like every escalation attempt;
stepper node expansion is bounded per conjecture. Successes pay the
escalated tier (3.0). No new event kinds.

**V5 — Trust unchanged, stated as a test.** The LLM's scripts and
moves are untrusted text; elaboration failures are discarded; the
final proof must survive `hasSorry`/`hasMVar` and `commitFact`'s full
ladder. The adversarial acceptance test (below) is a canned script
that "proves" via a minted axiom — the gate must refuse it, exactly as
`Smoke.lean` established for hand-built proposals.

**V6 — The instrument, fixed in advance.** A pinned corpus in the run
file: the deterministic matroid residual opens plus probe statements
for LLM-invented existential concepts, ~10 statements, half expected-
true, half from the false-but-unwitnessed class. Measurements: (i) the
control — repair-rung closures over the corpus; (ii) the comparison —
stepper closures over the same corpus, same LLM, same retrieval, same
budgets. Pre-registered claims: the repair rung closes ≥ 1 statement
the symbolic deep ladder cannot (if zero, that is the finding, as in
Arc 3); the stepper's closures ⊇ the repair rung's. No margin is
pre-committed for the stepper — the comparison table *is* the
deliverable, and a null result against the baseline's unfalsified
claim would itself be worth the arc.

**V7 — Out of scope.** Trained policies and embedding retrieval;
proof-term (non-tactic) generation; conversation beyond the one repair
round; parallel search; any change to gates, probes, or pricing beyond
V4's budgets.

## Acceptance tests (written before building)

1. **The repair loop works, deterministically** (`ProveStub.lean`, CI,
   canned transport): a planted statement fails the deep ladder; the
   canned model returns a broken script, then — given the error — the
   fixed one; admitted at the escalated tier through the gate.
2. **The gate refuses a poisoned proof** (`ProveStub.lean`): a canned
   script routing through a minted axiom type-checks and is refused by
   the axiom audit — this arc's Smoke.
3. **Retrieval finds the needed lemma** (`ProveStub.lean`): for a goal
   whose known proof uses lemma L, L is in the top-k.
4. **The control measurement** (`MatroidProveRun.lean`, live): the
   repair rung over the pinned corpus; closures recorded; ≥ 1 beyond
   the symbolic ladder or the zero is reported as the finding.
5. **The stepper works, deterministically** (`ProveStub.lean`, canned
   moves): closes a planted two-step goal that no single rung closes;
   certificate through the gate.
6. **The comparison** (`MatroidProveRun.lean`, live): stepper vs
   repair, same corpus, same budgets — the table.
7. **No regression**: the full suite passes with the new machinery off
   by default (by construction), and on with canned transports.

## Sequence

1. V2 retrieval (+ test 3).
2. V1 repair rung + `ProveStub` (+ tests 1–2, 7); the control run
   (test 4).
3. V3 stepper (+ test 5); the comparison run (test 6).
4. The report: the control vs the wager, on kernel-certified ground.
