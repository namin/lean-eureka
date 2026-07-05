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

## The omega run (`GraphGrandRun.lean`, live)

The first run with *every* capability on simultaneously — booth,
complement operator, compounder, invented-implications, tiers,
attracted credit, escalation, the in-population repair rung, the graph
refuter — on the second carrier. Twelve Bedrock calls, four
generations, audit clean, no agent deaths.

- **The booth invented 16 graph concepts with zero restatements**,
  against a canonical pool of only five predicates — the highest
  restatement pressure yet, and the model never fell into it. The
  inventions are a coherent slice of domination theory: simplicial /
  universal / twin / cut / pendant / support vertices, dominating and
  efficient-dominating sets, irredundant sets, modules, closed
  neighborhoods, induced matchings.
- **The compounder immediately composed over LLM vocabulary** — twelve
  depth-2 complement-products of booth concepts joined the pool
  (complement-dominating-sets, complement-modules, …), alongside the
  three canonical involutions certifying back
  (`compl_compl_IsVertexCover ≡ IsVertexCover`, …).
- **Corpus: 22 certified facts, all in invented vocabulary** — five
  alias bridges, fourteen witness-kit refutations of false invented
  implications (the kit works in vivo), three admitted invented
  implications. The booth finished alive at 0.15 with two vocabulary
  credits; the economy's matroid behavior reproduced exactly.
- **Honest null**: zero escalated-tier admissions — 83 conjectures
  stayed open, and four in-vivo repair attempts closed none. The
  booth's neighborhood-and-existential vocabulary outruns the prover on
  graphs just as it did on matroids; repair works on selected targets
  (REPORT_PROVE), not yet as a sweep tool. The open set is the
  standing worklist.

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
3. The omega run closes the arc's question and opens the next one:
   the system now reliably *invents faster than it proves* on every
   carrier — 16 sound new definitions, 83 open conjectures, 0 closed
   by search. The bottleneck is no longer architecture, economy, or
   generality; it is proof capacity on existential/neighborhood
   statements, which is where any future arc should spend (richer
   witness kits — path and cycle graphs — for refutation, and repair
   with domain-tuned prompts or the stepper with graph move sets for
   proof).

## Reproduction

```
lake env lean GraphRun.lean        # claims 1-5 (Mathlib, deterministic)
lake env lean GraphGrandRun.lean   # the omega run (Mathlib + Bedrock)
```
