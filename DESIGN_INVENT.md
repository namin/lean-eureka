# Concept invention: the design

Definitions as a gated proposal kind, with their own grounding
lifecycle. Organized as: the lifecycle, then the decisions (D1–D7),
then the acceptance tests, which were fixed before any code.

**Status: built (slice one).** Model: `Eureka/Gate.lean`
(`concept_birth_conservative`, `concept_birth_sound`, `defGated_sound`,
`defGated_concepts_invariant` — axiom-free, guarded in `Audit.lean`).
Runtime: `Eureka/Concepts.lean` (birth gate, reserved `Invented`
namespace + audit, certificate verdicts, tombstone+bridge merge,
re-probe triggers, budgeted sweep, conjunction/negated-conjunct
operators). Acceptance tests 2–6: `InventStub.lean` (in CI). Test 1,
the tower at birth: `MatroidInventStub.lean` (needs the Mathlib
build). Out of slice one, as ruled in D5/D7: compounding operators,
the yield-curve run at generative depth, the LLM booth stage, worth
for concepts (Arc 2).

## What this is

Today the engine proposes *facts* about a fixed vocabulary. Concept
invention adds a second kind of proposal: a *definition* (e.g.
`isLoopLike (M : Matroid α) (e : α) : Prop := ...`), which — if
admitted — extends the vocabulary that later conjectures may use.

The danger is known from the Python baseline (REPORT_ALIGN.md): left
unchecked, invented definitions pile into "synonym towers" — 3
reinvented variants of "loop", 4 of "cocircuit", ~91% of invented
vocabulary never tied to canonical Mathlib definitions. Verified, but
illegible.

The opportunity is new to this repo: the alias probe (does invented
`C` equal known `C'`?) used to cost ~75s per candidate, forcing the
baseline to align post-hoc. Here it is an in-process `MetaM` call
that runs in seconds (`MatroidStub` certifies `is_loop_def ↔ IsLoop`
through a chain). So we can afford to check identity **at birth**,
and keep checking it as the corpus grows.

## The lifecycle

A candidate definition moves through four stages:

1. **Screen.** Reject malformed candidates outright: sorry/mvars,
   non-`Prop`-valued shapes we can't probe, `partial`/`unsafe`/opaque
   defs (they can't unfold, so no probe rung can touch them), and any
   instance registration or attribute (a def landing in the simp set
   would poison the simp-with-corpus probe rung, which produces
   evidence). Refusals carry reasons — the baseline's 54%
   shape-mismatch/unparseable rate becomes visible refusals, not
   corpus residents.
2. **Birth.** `addDecl` of the def into a reserved namespace
   (`Invented.*`). The kernel checks well-formedness, exactly
   parallel to `commitFact`. An audit (style of `Audit.lean`) checks
   the reserved namespace contains only gate-admitted defs.
3. **Identity probe.** Try to certify the newborn against the known
   pool: defeq, `unfold`+`tauto`/`aesop`, chain through library iffs,
   implication sweep. The verdict (below) decides whether it joins
   the pool, merges, or is marked degenerate.
4. **Life in the pool.** A surviving concept can appear in
   conjectures and earn gated facts. Identity remains a standing
   obligation: the probe's power grows with the corpus, so "novel"
   is always "novel-so-far" and re-probes can merge it later.

A **merge** is not a deletion: the certified `C ↔ C'` is admitted as
an ordinary corpus fact (through the fact gate), `C` is tombstoned
(stops proposing), and its facts stay legible through the bridge.
The merge *is* a discovery — the tower's bricks become theorems.

## Decisions

**D1 — Where a concept lives.** Environment `def` in a reserved
namespace, plus an audit of that namespace. *Why:* `addDecl` makes
the kernel check the definition for free, and every existing probe
mechanism (`unfold`, simp-by-name, `isDefEq`) works unchanged;
the audit restores the gate boundary that raw env defs would blur.
The rejected alternative — corpus-only `Expr`s — keeps a crisper
boundary but forces new plumbing for every probe rung.

**D2 — What the model says.** Extend `Gate.lean` with a third
proposal kind. Model a concept as a *name for an already-expressible
statement-former*: a def is delta-expandable, so `Holds` is
unchanged and conservativity ("concept birth preserves corpus
soundness") is near-definitional. That is fine — the theorem's
payload is fixing the runtime's vocabulary and extending
`discovery_provenance` to concept-vocabulary facts, not depth.
Model first, runtime second, as with facts and rules.

**D3 — Identity as a standing obligation.** Probe at birth, then
re-probe on two triggers: (i) admission of a fact mentioning ≥ 2
invented predicates (cheap name scan), and (ii) a **budgeted**
periodic sweep — cheap syntactic pre-filter (head symbol, arity,
quick `isDefEq` under a small heartbeat cap) before any tactic
probe, K pairs per generation, round-robin over the rest. The sweep
is O(n²) in unmerged concepts; the budget is what keeps it CI-able.
Merge = tombstone + bridge (never canonicalizing rewrites of the
corpus).

**D4 — Verdicts are certificates.**

| verdict | evidence |
|---|---|
| alias | certified `C ↔ C'` (defeq, probe, or chain) |
| specializes | certified `C → C'` edge |
| generalizes | certified `C' → C` edge |
| degenerate | alias to a trivial target (⊤/⊥ seeded in the pool) |
| novel-so-far | none — names the non-monotonicity honestly |

Degenerate earns its row because conjunction/negation operators
constantly produce provably-empty or provably-universal predicates
(AM's classic failure mode). Seeding ⊤/⊥-shaped targets into the
probe pool catches them with the existing alias machinery — no new
mechanism.

**D5 — Generative operators, slice one.** Conjunction,
negated-conjunct (`P ∧ ¬Q`), dualization, singleton-lift, over the
`collectPredicates` pool. Depth cap 2; invented concepts do **not**
re-enter the operator pool yet (compounding is slice two). Metrics
fixed in advance, per generative depth: candidates, alias-at-birth,
spec/genl edges, degenerate rate, refuted-conjecture rate, facts
earned. This yield curve is the experiment's deliverable.

**D6 — Proposer staging.** Deterministic templates first (CI-able
stub), LLM booth later — same staging as facts → heuristics. With
merge-at-birth cheap, correctness lives entirely in the gate; the
prompt's only job is efficiency (fewer wasted proposals).

**D7 — No worth for concepts in slice one.** The economy experiment
(`MatroidEconomyRun`) showed the admissions-only worth function
cannot even see refutations; concept-worth built on it would inherit
the distortion. Agents keep the worth; concepts are corpus-adjacent
structure. Repricing (should merges and refutations pay?) is Arc 2,
with the D5 yield curve as its input data.

## Acceptance tests (written before building)

Test 1 lives in `MatroidInventStub.lean`; tests 2–6 in
`InventStub.lean` (CI).

1. **Tower examples merge at birth.** Feed the baseline's literal
   inventions (`is_loop_specialized`, `loop_as_dual_coloop`,
   `cocircuit_as_dual_circuit`, …): every one merges with a
   certificate naming its canonical target — the baseline's entire
   post-hoc alignment result, reproduced in-process at birth.
2. **A genuine novel survives** the probe, joins the pool, and earns
   a gated fact.
3. **Malformed candidates are refusals with reasons**, not corpus
   residents.
4. **Re-probe fires:** a pair whose alias is only provable via a
   later corpus fact gets merged by trigger (i).
5. **Degenerate caught at birth:** a provably-empty conjunction is
   verdicted degenerate, not novel.
6. **The audit bites:** a heuristic that `addDecl`s a def directly
   into the reserved namespace, bypassing the gate, is caught —
   `Smoke.lean`'s adversarial treatment, applied to concepts.

## Sequence

- [x] D2: model extension in `Gate.lean` + `Audit.lean` entry.
- [x] D1 + D3/D4: birth gate, namespace audit, probe verdicts, merge.
- [x] D5 (conjunction/negated-conjunct generic; dualization with the
      matroid domain) + tests 1–6 as deterministic stubs.
- [ ] The yield-curve run at generative depth.
- [ ] D6: LLM booth stage.

## Out of scope

Worth repricing (Arc 2); booth prompt design; compounding operators
(slice two); cross-domain generalization beyond `collectPredicates`;
deeper iff-graph search.
