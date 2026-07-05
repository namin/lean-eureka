# REPORT: concept invention, slice one (lean-eureka)

Definitions as a gated proposal kind, built to `DESIGN_INVENT.md` and
measured on four runs: the baseline's synonym tower replayed at birth,
the lifecycle acceptance tests, a live LLM concept booth, and the
yield-curve enumeration of the D5 operator set. Every number below that
says "certified" is a fact the kernel checked through the ordinary gate
(screen → `addDecl` → axiom audit).

## Setup

- Model extension (`Eureka/Gate.lean`): concepts as a third proposal
  kind; `concept_birth_conservative`, `concept_birth_sound`,
  `defGated_sound`, `defGated_concepts_invariant` — axiom-free, guarded
  in `Audit.lean`.
- Runtime (`Eureka/Concepts.lean`): birth gate into the reserved
  `Invented` namespace (kernel-checked, axiom-audited, name-clash
  refused), `auditInvented` for the namespace boundary, identity probes
  over folded + delta-expanded forms, verdicts as certificates
  (alias / degenerate / specializes / generalizes / novel-so-far),
  merge = tombstone + bridge, re-probe trigger (i) and the budgeted
  sweep (ii), conjunction/negated-conjunct operators; dualization and
  singleton-lift with the matroid domain
  (`EurekaMathlib/MatroidDisco.lean`).
- Booth (`Eureka/ConceptBooth.lean`): the LLM proposes definitions in a
  `name | shape | body` line format, elaborated at the declared shape's
  type; per-candidate fates feed back into the next round's prompt.
- Probe economy knobs (`ProbeCtx`): per-attempt heartbeat budget,
  alias-only births, invented-target window — all default-off, all
  logged by the runs that use them.

## Run A — the tower at birth (`MatroidInventStub.lean`)

The literal inventions from the formal-disco baseline's matroid runs
(REPORT_ALIGN's synonym tower), fed to the birth gate as candidates,
plus one dualization-operator product. **7 of 7 merged at birth**, each
with a kernel-checked bridge naming its canonical target:

| invented (baseline) | canonical | certificate |
|---|---|---|
| `loop_element` | `Matroid.IsLoop` | chained via `Matroid.singleton_dep` |
| `is_loop_specialized` | `Matroid.IsLoop` | chained via `Matroid.singleton_dep` |
| `loop_as_dual_coloop` | `Matroid.IsLoop` | simp (expanded) |
| `cocircuit_as_dual_circuit` | `Matroid.IsCocircuit` | refl (folded) |
| `is_cocircuit_def` | `Matroid.IsCocircuit` | refl (folded) |
| `dep_invented` | `Matroid.Dep` | targeted simp only (conjunct swap) |
| `dual_IsCircuit` (operator) | `Matroid.IsCocircuit` | refl (folded) |

This is the baseline's entire Phase 1+2 alignment result — which ran
post-hoc at ~75s per probe and found the tower only after it had formed
— reproduced in-process, at birth, before any duplicate joins the pool.
The tower's bricks enter the corpus as seven theorems.

## Run B — lifecycle acceptance on `Nat` (`InventStub.lean`, in CI)

Acceptance tests 2–6 from the design, deterministic: 10 candidates —
4 refused with reasons (non-`Prop`, sorry, metavariables, name clash),
`2 ∣ n` merged into `isEven` by omega and a byte-identical rename by
refl, the operator product `isEven ∧ isOdd` certified degenerate (⊥),
`isEven ∧ isSmall` survived as novel and earned 2 specializes-edges.
The budgeted sweep before the unlock merged nothing (honest silence);
after an enabling corpus fact, the newly provable edge between the
stuck pair — a fact mentioning two invented predicates — fired re-probe
trigger (i) and merged the younger into the elder. A def smuggled into
the reserved namespace by raw `addDecl` was flagged by the audit.
Corpus: 10 certified facts.

## Run C — the live concept booth (`MatroidInventRun.lean`)

Claude (Sonnet, Bedrock) proposing matroid definitions; 2 rounds × 4,
canonical pool and per-round fates in the prompt. **8/8 parsed and
born; 0 refused, 0 degenerate, 0 merged at birth; 8 novel-so-far; 2
certified edges** (`MatroidIsCircuitHyperplane → IsCircuit`,
`MatroidIsFreeFlat → Indep`). The inventions are mathematically natural:
parallel/series partners via singleton closures, cyclic sets, cyclic
flats, circuit-hyperplanes, separators, free flats.

Zero merged at birth is the notable cell: with existing vocabulary
visible and fates fed back, the model never restated a canonical
predicate — the prompt did the efficiency work, and the gate had
nothing to catch. (The run also surfaced one real bug: candidate
elaboration lacked a heartbeat re-baseline and crashed round 2 on the
cumulative budget; it now runs under the same guard as every probe.)

## Run D — the yield curve (`MatroidYieldRun.lean`)

The fixed D5 operator set, exhaustively, over the 9 predicates
extracted from the `Matroid` namespace (2 element-shaped, 7
set-shaped); 82 products, every one through the lifecycle. Economy,
logged: 2000-heartbeat probe budget, alias-only births (edges measured
once, in the facts phase, with the refuter), invented-target window 12
(the tail belongs to the sweep).

| operator | candidates | alias at birth | degenerate | novel-so-far |
|---|---|---|---|---|
| dualize | 9 | **6** | 0 | 3 |
| singleton-lift | 7 | **3** | 1 (⊤) | 3 |
| conjunction | 22 | 0 | 0 | 22 |
| negated-conjunct | 44 | 1 | 0 | 43 |

The alias column is where the structure lives — those merges are
theorems: the full duality involution (`dual_Indep ≡ Coindep` by refl,
`dual_Coindep ≡ Indep` and `dual_IsColoop ≡ IsLoop` through
`dual_dual`, the circuit/cocircuit swap both ways), and the
singleton-lift bridges (`elem_Dep ≡ IsLoop` — `singleton_dep`
rediscovered as an operator product — `elem_IsCircuit ≡ IsLoop`,
`elem_IsCocircuit ≡ IsColoop`). `elem_IsRkFinite` was certified ⊤
(singletons have finite rank) — the degeneracy verdict earning its
keep. The one negated-conjunct alias is absorption the probes could
see: `Dep ∧ ¬Indep ≡ Dep` by `unfold; tauto`.

The novel survivors of dualize/lift are real vocabulary the pool
lacked: `dual_Dep` (codependence), `dual_IsBase` (cobase),
`elem_Indep` (nonloop), `elem_IsBase` (singleton base). The boolean
operators' 65 "novel" products are a different population: mechanical
combinations, including absorption aliases the alias-only economy
cannot see (`Indep ∧ IsBase ≡ IsBase` needs one directional ladder plus
`IsBase.indep`) — classified novel-so-far, correctly re-probeable, and
a measured cost of the economy rather than a silent one.

Facts phase (survivor × canonical implications, both directions,
`probeProve` for proof and the invented-aware refuter for
counterexamples): **[PENDING — run in progress]**

## Baseline comparison

| | formal-disco (baseline) | lean-eureka (this slice) |
|---|---|---|
| identity check | post-hoc, ~75s/probe, subprocess | at birth + standing obligation, in-process |
| grounding outcome | 13 of ~200 invented aliased, found late; 3 loop + 4 cocircuit variants coexisted | tower merges at birth, 7/7 certified; duplicates cannot join the pool |
| spec/genl relations | classified, uncertifiable | certified implication edges |
| degenerate concepts | unpriced | certified ⊤/⊥ verdicts |
| LLM restatement rate | high (the tower formed freely) | 0/8 in the live booth (pool + fates in prompt) |

## Interpretation (separate from the facts above)

1. **Grounding moved from analysis to architecture.** The baseline's
   central unsolved problem — verified-but-illegible vocabulary — is
   answered by making identity a birth obligation. Nothing here made
   the probes smarter than the baseline's tactics; what changed is
   *when* they run and what happens on success (a certificate in the
   corpus and a tombstone, not a report).
2. **The yield concentrates in structure-aware operators.** Dualization
   and singleton-lift ground two-thirds and half of their products
   respectively — and those aliases are the discoveries (the duality
   involution, the loop bridges). The boolean operators produce almost
   nothing but unmergeable novelty. That is AM's yield-decay claim
   visible at depth 1, and it says slice two's compounding should feed
   structure-aware operators, not boolean closure.
3. **The booth's economics held.** Correctness in the gate freed the
   prompt to do efficiency, and the live model — unlike the baseline's
   — invented no synonyms. Its concepts are also qualitatively beyond
   the operators' (cyclic flats vs. conjunctions), which is the case
   for the booth as the generative engine with templates as the
   control.
4. **Honest limits.** "Novel-so-far" is relative to the extracted pool
   and the rungs' reach: absorption aliases hide among the boolean
   survivors by configuration, and the LLM's existential bodies exceed
   the current probes entirely. No invented concept has yet earned a
   fact of depth — the definition-that-pays-for-itself test is slice
   two's question, after compounding and a deeper prover. The worth
   economy still cannot see invention events (Arc 2).

## Reproduction

```
lake env lean InventStub.lean          # acceptance 2–6 (CI)
lake env lean InventBoothStub.lean     # booth pipeline, canned transport (CI)
lake env lean MatroidInventStub.lean   # the tower at birth (Mathlib)
lake env lean MatroidInventRun.lean    # live booth (Mathlib + Bedrock)
lake env lean MatroidYieldRun.lean     # yield curve (Mathlib; streams to yield-progress.log)
```

Lean buffers `#eval` output until a command completes; the yield run
streams per-candidate progress to `yield-progress.log` for that reason.
