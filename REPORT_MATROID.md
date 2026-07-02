# REPORT: matroid runs (lean-eureka)

2026-07-02. Companion to formal-disco-eurisko-verified's `REPORT_MATROID.md`
/ `REPORT_ALIGN.md`, on the same domain, answering the same questions with a
different architecture: discovery loop inside Lean (`MetaM`), kernel as
in-process gate, grounding as a first-class evidence path.

Raw numbers first; interpretation at the end, separately.

## Setup

- **User guidance: one name — `Matroid`.** No seed file, no curated
  canonical pool, no prompt curation. (Baseline required `seed_matroid.json`
  + `canonical_matroid_mathlib.json` + hand-tuned worth boosts.)
- Predicate pool, extracted from the namespace by signature shape:
  9 predicates — `Coindep`, `Dep`, `Indep`, `IsBase`, `IsCircuit`,
  `IsCocircuit`, `IsRkFinite` (set-shaped); `IsColoop`, `IsLoop`
  (element-shaped).
- Grounding pool: 1314 `Matroid.*` theorems, keyed by (binders, relation,
  side heads), universe-instantiated at `Level.zero`.
- No counterexample search exists for this domain: false conjectures land
  in `open`, not `refuted`. Every `open` below means exactly
  "unrefuted and unproved".
- Toolchain `leanprover/lean4:v4.30.0`, Mathlib tag `v4.30.0`. LLM: Claude
  Sonnet on Bedrock (booth rounds only; all other runs deterministic).

## Run A — microcosm (`MatroidStub.lean`)

Implication sweep over same-shape ordered pairs (44 conjectures):

| outcome | count | facts |
|---|---|---|
| admitted, grounded | 2 | `IsBase → Indep` (`Matroid.IsBase.indep`), `IsCircuit → Dep` (`Matroid.IsCircuit.dep`) |
| open | 42 | — |

Alias probes on invented predicates taken from the baseline run's synonym
tower:

| invented predicate | verdict | certificate |
|---|---|---|
| `dep_invented` (`X ⊆ M.E ∧ ¬M.Indep X` — `Matroid.Dep` with conjuncts swapped) | certified alias of `Matroid.Dep` | `by unfold dep_invented Matroid.Dep; tauto` |
| `is_loop_def` (`e ∈ M.E ∧ ¬M.Indep {e}` — the baseline's literal invented loop predicate) | certified alias of `Matroid.IsLoop` | composed: direct step to `M.Dep {e}` (unfold + aesop), chained through `Matroid.singleton_dep` with `Iff.trans` |

Both probes run in-process (`MetaM` against the loaded environment); the
baseline's equivalent probe was a `lake env lean` subprocess at ~75s per
candidate (BRAINSTORM_ALIGN facet 1.B), applied post-hoc.

## Run B — discovery (`MatroidDiscoRun.lean`)

Population engine (4 template agents: implications, exclusions, duality,
singleton; 3 generations, judge budget 30/generation, `Matroid` grounding
pool), then LLM booth (2 rounds, 6 proposals requested per round).

Totals: **19 admitted (all kernel-gated, each with a certificate), 83 open,
0 refuted, 0 refused at the gate.**

Template phase (8 admitted):

- singleton agent (3): `IsLoop ↔ Dep {e}` (`singleton_dep`),
  `IsLoop ↔ IsCircuit {e}` (`singleton_isCircuit`),
  `IsColoop ↔ IsCocircuit {e}` (`singleton_isCocircuit`);
- duality agent (2): `M✶.Coindep ↔ M.Indep` (`dual_coindep_iff`),
  `M✶.Indep ↔ M.Coindep` — **by `refl`**: definitional;
- exclusions agent (3): `Dep → ¬Indep`, `Indep → ¬Dep`,
  `IsCircuit → ¬Indep` (all grounded).

Kill event: the implications agent was killed at worth 0.03 after 16
judged, all open — its enumeration prefix (`Coindep`-first, alphabetical)
contains no theorems, and it died before reaching `IsBase → Indep`, which
it provably had queued (Run A admits it). Same-shaped event in the
Run C agenda variant (exclusions killed at 0.04 after 40 judged, 1
admitted).

LLM booth phase: 12 fresh proposals, **11 admitted** (9 grounded, 2 refl),
1 open, 0 falsehoods, 0 unparseable. Notable:

- `M.IsBase B → M✶.IsBase (M.E \ B)` — grounded:
  `Matroid.IsBase.compl_isBase_dual`. (The baseline's ×100-boosted
  Whitney-duality target family; it failed there after 500 attempts. Note
  the claim difference: the baseline tried to *prove* it; here it was
  *recognized* — certified by grounding, not derived.)
- `M.IsCocircuit X ↔ M✶.IsCircuit X` and `M.IsColoop e ↔ M✶.IsLoop e` —
  by `refl` (definitional discoveries).
- the ground-set family (`Indep X → X ⊆ M.E`, etc., 5 facts) and
  `IsColoop e → IsBase B → e ∈ B` (all grounded).
- the one open: `M.IsColoop e → M.Indep {e}` — true; composition-provable
  after Run C's rung existed (it ran before).

## Run C — frontier harvest (`MatroidFrontierRun.lean`)

Complete sweep of the exclusion family `P X → ¬Q X` (44 conjectures) with
the composition rung (bounded backward chaining, depth 2, certificates name
every lemma used):

**4 grounded + 8 composed + 32 open.**

The 8 composed facts — kernel-certified, and *not matched by the grounding
pass* over the 1314-lemma `Matroid.*` pool (grounding is attempted first
and finds no alias; this is a claim about the pool, not an exhaustive
search of Mathlib):

| fact | certificate |
|---|---|
| `Coindep X → ¬IsCocircuit X` | composed: `Dep.not_indep + IsCircuit.dep` |
| `Dep X → ¬IsBase X` | composed: `Dep.not_indep + IsBase.indep` |
| `Indep X → ¬IsCircuit X` | composed: `Dep.not_indep + IsCircuit.dep` |
| `IsBase X → ¬Dep X` | composed: `Dep.not_indep + IsBase.indep` |
| `IsBase X → ¬IsCircuit X` | composed: `Dep.not_indep + IsBase.indep + IsCircuit.dep` |
| `IsCircuit X → ¬IsBase X` | composed: `Dep.not_indep + IsBase.indep + IsCircuit.dep` |
| `IsCocircuit X → ¬Coindep X` | composed: `Dep.not_indep + IsCircuit.dep` |
| `IsColoop e → ¬IsLoop e` | composed: `IsNonloop.not_isLoop + IsColoop.isNonloop` |

Mechanical observations (facts, from the certificates):

- The `Coindep`/`IsCocircuit` facts are proved by *circuit* lemmas:
  unification instantiated the matroid metavariable at `M✶` — the argument
  ran in the dual without any duality-aware code.
- `IsColoop → ¬IsLoop` routes through `IsNonloop`, which is not in the
  9-predicate conjecture pool: the evidence pool (1314 lemmas) is wider
  than the hypothesis pool.
- The three-lemma routes differ from the obvious two-lemma proofs
  (`hC.not_indep hB.indep`): the search found its own path.

## Baseline comparison

Sources: formal-disco-eurisko-verified `REPORT_MATROID.md`,
`REPORT_ALIGN.md`, `BRAINSTORM_ALIGN.md`. **The systems' objectives
differ** — the baseline invents *concepts* (144 invented predicates) and
proves theorems about them; lean-eureka (today) conjectures over existing
predicates. Rows are only comparable where the question is the same.

| question | baseline (formal-disco, May 2026) | lean-eureka (this report) |
|---|---|---|
| user guidance | seed JSON + canonical pool JSON + worth surgery by hand | the name `Matroid` |
| verification | `lake env lean` subprocess per attempt | kernel in-process (`addDecl` + axiom audit) |
| corpus soundness | per-proof check | model-level theorem (`discovery_sound`, machine-checked); runtime instantiates the gate (no formal refinement proof) |
| alias detection | post-hoc toolchain, ~75s/probe, ~9% of invented vocab grounded | at admission, in-process; both probed synonym-tower predicates certified (one via transitive chain) |
| synonym tower | 3 loop + 4 cocircuit variants entered the corpus | definitional duplicates merged at proposal time, logged with targets |
| Whitney-duality family | targeted ×100 boost, failed after 500 attempts | `IsBase B → M✶.IsBase (M.E \ B)` certified — by grounding (recognized, not derived) |
| new-to-library facts | theorems about invented concepts (LLM-proved) | 8 composed exclusion facts, unmatched by the grounding pass |
| falsehood filtering | `plausible` counterexample subprocess | none in this domain (32–83 opens include falsehoods) |
| priority starvation | diagnosed post-hoc, fixed by hand-tuned boost | reproduced mechanistically 3× (kill rule vs enumeration order); resolved for completeness questions by sweeping instead |

## Interpretation (separate from the facts above)

1. The system is a working *verified rediscovery, grounding, and shallow
   composition* engine. Its new-as-unmatched output on matroids is the
   composed exclusion lattice — modest mathematics, honestly labeled
   (unmatched by the grounding pass, not proven absent from Mathlib), found
   and certified autonomously.
2. Grounding-first discovery changes what "depth ceiling" means: the
   baseline's unprovable duality target became a recognition problem. This
   routes *around* the ceiling rather than through it; deriving such facts
   from axioms remains beyond both systems.
3. The kill-rule/enumeration-order interaction is a real design tension:
   in refuter-free domains, worth economics trade completeness for
   attention. A refuter (finite-matroid enumeration) would convert most
   opens to refuted and largely dissolve the tension.
4. The remaining gap to the baseline's ambition is concept invention:
   proposed definitions with their own grounding lifecycle. Everything
   above operates on Mathlib's vocabulary.

## Reproduction

```
lake build EurekaMathlib
lake env lean MatroidStub.lean        # Run A (deterministic)
lake env lean MatroidDiscoRun.lean    # Run B (needs aws CLI + Bedrock)
lake env lean MatroidFrontierRun.lean # Run C (deterministic)
```

Runs A and C are deterministic given the Mathlib pin; Run B's booth rounds
depend on live LLM output (template phase deterministic).
