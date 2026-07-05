# REPORT: the graph domain (lean-eureka, the generalization arc)

DESIGN_GRAPH's question — discovery system or matroid program? — put to
a deterministic instrument: the whole stack on `SimpleGraph`, with the
per-domain surface deliberately limited to the complement operator, a
witness kit, and agent wrappers. All five pre-registered claims hold;
one hidden assumption surfaced and is recorded (claim 6). Every
"certified" below is a kernel-gated fact.

## The run (`GraphRun.lean`, deterministic)

**Claim 1 — extraction generalizes.** `collectPredicates SimpleGraph`
found five set/element-shaped predicates with zero graph-specific
code: `IsClique`, `IsIndepSet`, `IsIsolated`, `IsTutteViolator`,
`IsVertexCover`. Grounding pool: 3110 `SimpleGraph.*` lemmas.

**Claim 2 — the involution grounds at birth.**
`compl_IsClique ≡ IsIndepSet` (grounded: `isClique_compl`) and
`compl_IsIndepSet ≡ IsClique` (grounded: `isIndepSet_compl`) — the
exact analog of `dual_IsCircuit ≡ IsCocircuit`, certificates naming
the library bridges.

**Claim 3 — compounding rhymes.** Three depth-2 involution products
merged back into canonical vocabulary
(`compl_compl_IsIsolated ≡ IsIsolated`, likewise for `IsTutteViolator`
and `IsVertexCover`, via `compl_compl`) — the `dual_dual_Dep ≡ Dep`
pattern, new carrier, same machinery, same depth cap and alias decay.

**Claim 4 — the refuter generalizes.** The graph witness kit (`⊥`/`⊤`
on ℕ, tiny sets, a pairwise simp vocabulary — the matroid kit's
pattern) certified five refutations.

**Claim 5 — the economy carries over.** The complementer earned its
certified aliases; unmergeable novelty earned nothing; audit clean.

The novel survivors are real vocabulary: `compl_IsIsolated` (isolated
in the complement — a dominating vertex), `compl_IsVertexCover`,
`compl_IsTutteViolator` — none in the extracted pool, all now probeable
citizens.

**Claim 6 — the surfaced assumption.** The run's first take produced
*zero* proposals: matroid duality is a plain function (`Matroid.dual`),
so the operator template built its value with `mkAppM`; graph
complement arrives through the Boolean-algebra instance hierarchy,
which raw `mkAppM` synthesis does not resolve — only full elaboration
does. The operator now builds values by elaborating source text
(`elabTermAt`, `@`-application for canonical/invented uniformity).
One assumption, found by a pre-registered exact-target assertion,
fixed at the domain layer, core untouched.

## Interpretation (separate from the facts above)

1. **The stack is a discovery system, not a matroid program.** The
   entire per-domain cost of a new carrier was ~120 lines: one
   operator, six named witnesses with their simp vocabulary, two agent
   wrappers. Extraction, probes, verdicts, merges, economy,
   escalation, and even `inventedImplAgent` ran unchanged.
2. **Structure-aware operators travel.** The matroid finding — value
   concentrates in involution-like operators — reproduced exactly:
   complement grounded 2/5 at depth 1 and 3/3 involutions at depth 2,
   and its unmerged products are the interesting vocabulary.
3. What a fuller graph arc would add: the LLM booth on graphs
   (`GraphGrandRun`), degree/neighborhood-shaped predicates beyond the
   3-binder extraction shape, and a richer witness kit (path and cycle
   graphs) for the refuter.

## Reproduction

```
lake env lean GraphRun.lean   # Mathlib, deterministic
```
