# REPORT: depth (lean-eureka, Arc 3)

Built to `DESIGN_DEPTH.md`: difficulty priced by the rung that proved
it, attracted credit for concepts that draw certified structure, and a
budgeted escalation pass that re-judges the open set with a deep
ladder. The pre-registered acceptance test for escalation failed three
times before it passed — and each failure was a real defect, one of
them a library bug that had been silently degrading the prover since
slice one. That diagnostic chain is the report's spine; every
"certified" below is a kernel-gated fact.

## Setup

- `Eureka/Worth.lean`: `Tier` (cheap / standard / deep / escalated)
  classified from the rung string; cheap and standard pay 1.0 — so
  every pre-depth instrument holds by construction — deep 2.0,
  escalated 3.0; `conceptAttracted` (0.5, attention-free) pays a
  concept's inventor when a certified bridge lands on it, at birth-
  alias and re-probe-merge sites, prober excluded.
- `Eureka/Concepts.lean` (`escalate`), `Eureka/Prover.lean`
  (`tryTacticClosed`, parameterized compose depth), `Eureka/Evolve.lean`
  (the open set; a per-generation escalation pass, budget-bounded,
  invented-vocabulary first, breadth before retries, 2 tries per
  conjecture; failures charge the proposer an attention, successes pay
  at the escalated tier).

## The deterministic suite (`DepthStub.lean`, CI)

The tier classifier maps every rung family correctly; at equal
admission volume a deep prover out-earns a standard one. The induction
rung proves `∀ n, double2 n = 2 * n` — open on the cheap ladder
(refutation silent, simp equations blocked on the opaque argument,
omega sees an atom) — and the proof is gate-admitted at the escalated
tier. The vindication replay: an inventor killed for garbage is paid
`conceptAttracted` when another agent's clone merges into its concept.
Escalation inside a population closed 4 of 6 planted opens at the
escalated tier. All green, in CI.

## Test 1: five takes, three defects, then the pass

`MatroidDepthRun.lean` — dualizer, compounder, invented-implications
(no LLM), cheap ladder at 5000 heartbeats, escalation budget 8 over a
deep ladder with ambient budget, `Set.*` joining the grounding pool
(1314 → 6041 lemmas), composition depth 3.

- **Take 1 — 0 escalated.** Diagnosis: the escalation queue was
  insertion-ordered with retries eligible, so two generations escalated
  the same stuck head-of-queue family twice each and never reached the
  provable statements deeper in. *Fix: breadth before retries.*
- **Take 2 — 0 escalated,** full coverage. Hand-dissection of a
  statement that *should* compose (`M.IsCocircuit K → dual_Dep M K`
  via `IsCircuit.dep`) found the real bug: `expandConsts` substituted
  definitions at the leaf constant, leaving the enclosing application
  headed by a lambda. The surviving beta-redex defeated every
  head-indexed rung — compose, known, chain — on *every expanded form
  since slice one*. Simp-based rungs beta-reduce their goals, which is
  why aliases kept working and the defect stayed invisible. *Fix:
  rewrite at application nodes; collapse redexes created by inner
  rewrites.* All eleven CI stubs pass unchanged under the fix —
  consistent with the bug only ever suppressing provers, never
  unsoundly admitting (refusal is safe; that is the gate architecture's
  point).
- **Take 3 — 0 escalated, for the best reason:** the beta fix made the
  *cheap* ladder close the flagship at judge time — a four-lemma
  composition, paid at the deep tier — so it never reached the open
  set. The residue contained one more provable statement:
  `dual_IsBase a → Coindep a` (a dual base is dual-independent), whose
  only route runs *through* the iff-shaped `coindep_def` — a compose
  rung gap.
- **Take 4 — 0 escalated.** The chosen fix — making the canonical
  definitional layer transparent under escalation — backfired:
  `IsBase` and `Indep` are structure projections, and their expansion
  is proj-headed, defeating head-indexing exactly as the beta-redexes
  had. *Fix: the const-headed-body rule — expand only canonical defs
  whose stripped value is headed by a constant (wrapper defs like
  `Coindep`, `IsCocircuit`), never projections.*
- **Take 5 — pass.** Escalation admits
  `∀ M a, Invented.dual_IsBase M a → M.Coindep a` at the escalated
  tier (`composed: Matroid.IsBasis.indep + Matroid.IsBase.isBasis_ground`),
  gate-checked, audit clean; 20 certified refutations stand; the
  remaining opens (the `dual_IsRkFinite` family and the false-but-
  unwitnessed) rest honestly.

## Interpretation (separate from the facts above)

1. **Head-indexing is the prover's central economy, and everything that
   breaks it is invisible until something demands depth.** Three
   independent defects — queue starvation, beta-redexes, proj-headed
   expansion — all presented identically (zero closures), and only a
   pre-registered assertion that refused to pass turned them into
   diagnoses. The methodological lesson is the arc's real product: the
   acceptance test was worth more than the feature.
2. **The beta fix is retroactive capability.** Compose/known/chain now
   fire on expanded forms everywhere — the cheap ladder closing the
   flagship at 5000 heartbeats is the direct measure. Earlier runs'
   "open" counts (the yield facts phase, the grand run) are now
   overestimates of the ladder's true ceiling.
3. **Known gap, deliberately deferred:** composing through iff-shaped
   bridges on implication goals. Canonical transparency works around
   the definitional cases; a proper rung (iff lemmas as paired
   implications inside `proveFrom`) is the next ladder upgrade,
   alongside DESIGN_DEPTH P7's LLM proof repair.

## Reproduction

```
lake env lean DepthStub.lean         # tests 2–4 (CI)
lake env lean MatroidDepthRun.lean   # test 1 (Mathlib, deterministic)
```
