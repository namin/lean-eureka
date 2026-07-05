# The graph domain: the generalization arc

Not a new design — the application of every ruled design (DESIGN_INVENT,
DESIGN_WORTH, DESIGN_DEPTH, DESIGN_PROVE) to a second carrier,
`SimpleGraph`, with the generality claims pre-registered. The question
this arc answers: is the stack a discovery system, or a matroid
program?

**Status: verified.** Claims 1–5 hold on `SimpleGraph`
(`GraphRun.lean`, REPORT_GRAPH.md); claim 6 surfaced exactly one hidden
assumption — operator values must be built by *elaboration*, not raw
`mkAppM`, because instance-derived structure (graph complement via the
Boolean-algebra hierarchy) is invisible to bare synthesis. Fixed at the
domain layer; the core was not touched.

## Why SimpleGraph

It has the structural feature that made matroids productive:
**complementation is an involution**, the exact analog of matroid
duality. `IsClique` and `IsIndepSet` are complement-duals
(`isClique_compl : Gᶜ.IsClique s ↔ G.IsIndepSet s`, simp-tagged in
Mathlib), and `IsIndepSet` is a reducible abbrev the way `IsCocircuit`
was. If the machinery generalizes, the graph run should *rhyme* with
the matroid record without a single new mechanism.

## What is per-domain, by design

The complement operator (`Gᶜ`, replacing dualize), the refuter's
witness kit (small concrete graphs — `⊥`, `⊤` on ℕ, small sets — with
their simp vocabulary), and the booth's shapes/blurb. Everything else —
extraction (`collectPredicates`), probes, verdicts, merges, the
economy, escalation, repair — is used as-is or the claim below fails.

## Pre-registered claims (the acceptance tests)

1. **Extraction generalizes**: `collectPredicates SimpleGraph` finds
   the set-shaped predicates with no graph-specific code.
2. **The involution grounds at birth**: `compl_IsClique` merges into
   `IsIndepSet` and `compl_IsIndepSet` into `IsClique`, certified — the
   graph analog of `dual_IsCircuit ≡ IsCocircuit`.
3. **Compounding rhymes**: depth-2 `compl_compl_X` merges back into
   canonical `X` (the involution, as in `dual_dual_Dep ≡ Dep`), under
   the same depth cap and alias decay.
4. **The refuter generalizes**: a graph witness kit (named concrete
   graphs + simp vocabulary, the matroid kit's pattern) certifies at
   least one refutation of a false invented-vocabulary implication.
5. **The economy carries over unchanged**: the complementer earns via
   certified aliases; unmergeable novelty earns ≈ 0; audit clean.
6. **Every place the code secretly assumed "matroid" surfaces as a
   failure and is recorded here** — the failures are the arc's data as
   much as the passes.

Deterministic instrument: `GraphRun.lean` (claims 1–5). Live booth on
graphs (the LLM inventing graph vocabulary, zero restatements expected)
as the optional second instrument, `GraphGrandRun.lean`.

## Out of scope

New operators beyond complement; graph-specific prover rungs; any
change to gates, probes, pricing, or search.
