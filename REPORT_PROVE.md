# REPORT: proof search (lean-eureka, Arc 4)

Built to `DESIGN_PROVE.md`: premise retrieval, the LLM repair rung (the
control), and the tactic-state stepper (the wager), measured against
each other on a pinned corpus. Headline: **the system's first
LLM-proved fact** — an existentially-quantified statement about an
invented concept, closed by the repair loop's *feedback round* where
every symbolic rung fails — and a null first result for the wager.
Every "certified" below is a kernel-gated fact.

## Setup

- `retrievePremises` (`Eureka/Prover.lean`): symbol-overlap retrieval
  with document-frequency filtering (ubiquitous constants carry no
  signal) and size-normalized scoring. `tryTacticClosedErr` returns
  error text — the repair loop's food; `asByBlock` makes multi-line
  model scripts parse.
- `Eureka/Prove.lean`: `proveByRepair` (whole script, one repair round,
  two calls max) and `proveByStepper` (ordered DFS over tactic states
  via `Elab.runTactic`; cheap moves exhaust before the model is
  consulted as a move generator on the rendered goal; node budget,
  depth cap, call cap). Both LLM-optional, both untrusted: the axiom
  audit is the script screening (a canned proof via a minted axiom
  elaborates and dies at the gate — this arc's Smoke, in CI).
- Wired into `evolve`'s escalation pass behind `proofCall` +
  `llmProofBudget` (off by default; the full pre-existing suite passes
  by construction).

## The deterministic suite (`ProveStub.lean`, CI)

Retrieval puts `Nat.gcd_self` in the top-k for a gcd goal. The repair
loop recovers from a planted broken script — the second prompt
demonstrably carries the failure feedback — and the repaired induction
proof passes the gate. The poisoned script dies at the axiom audit.
The stepper closes a two-step goal no single rung closes, cheap moves
alone verifiably failing first. All green, in CI.

## The control and the comparison (`MatroidProveRun.lean`, live)

Pinned corpus over LLM-style inventions (the cyclic-set and free-flat
predicates the grand runs' booth actually produces, plus the hard
dual-rank residual family). Seven Bedrock calls total.

| statement | symbolic | repair | stepper |
|---|---|---|---|
| `IsCircuit X → MIsCyclic M X` | open | **✓ round 2** | open |
| `MIsFreeFlat → Indep` | ✓ tauto | — | — |
| `MIsCyclic ↔ MIsCyclic` (sanity) | ✓ refl | — | — |
| `IsRkFinite → dual_IsRkFinite` | open | open | open |
| `dual_IsRkFinite → IsRkFinite` | open | open | open |
| `Indep → MIsFreeFlat` | ✗ refuted (loopyOn) | — | — |

- **Test 4, the control: passed, with the best possible witness.**
  `M.IsCircuit X → MIsCyclic M X` — every element of a circuit lies on
  a circuit inside it, an ∃-introduction under two binders about an
  invented predicate — is exactly the statement class every symbolic
  rung has been unable to touch since the first grand run. The model's
  first script failed; the *repair round*, fed the error, succeeded;
  the proof passed screen, kernel, and audit. This is the system's
  first machine-proved (not merely machine-proposed) fact of the
  invention era.
- **Test 6, the wager: null on this sample.** The stepper closed
  nothing repair didn't; on the one contested statement it failed
  (4-call cap, 40 nodes, a cheap-move set tuned for `Nat`). The
  pre-registered claim — stepper closures ⊇ repair's — is *not*
  supported at n = 1 contested row. The baseline's
  interaction-beats-repair hypothesis is no longer default-true; it is
  now something an instrument can keep testing.
- The hard rows stayed honestly open on all three ladders, and the
  false row died at the witness kit, not at an LLM's say-so.

## Interpretation (separate from the facts above)

1. **The feedback round is the active ingredient** — the one live
   closure came on round 2, not round 1, matching the baseline's
   experience that repair (not generation) moves the proof rate. The
   in-process version costs 7 calls for a 6-row corpus.
2. **The wager's null is informative, not final**: one contested
   statement, a Nat-tuned move set, tight caps. If the stepper is
   pursued, the move set and budgets are the knobs — but the burden of
   proof now sits with interaction, which is the reverse of where the
   baseline's post-mortem left it.
3. **The trust story survived its strongest test yet**: model-authored
   proofs enter the corpus with no new screening — elaboration
   discards nonsense, and the axiom audit catches poison, demonstrated
   adversarially in CI. The proposer got smarter again; the gate did
   not grow again.

## Reproduction

```
lake env lean ProveStub.lean        # tests 1,2,3,5 (CI, canned)
lake env lean MatroidProveRun.lean  # tests 4,6 (Mathlib + Bedrock)
```
