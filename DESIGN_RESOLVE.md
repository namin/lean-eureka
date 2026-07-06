# Resolving the residue: moving the benchmark

The first use of the improvement loop the maintenance arc built: the
benchmark says 1 of 29, the residue splits into false-but-unwitnessed
and true-but-unproved, and each population has a known tool. Decisions
K1–K5, claims pre-registered.

**Status: built and measured.** B1 ✓ (12 certified refutations of the
v1 residue — unlocked chiefly by the transitive-unfold fix,
`inventedUnfoldNames`, which the kits exposed: depth-2 concepts left
their parents folded for every refuter). B2 ✓ (corpus v2, full-coverage
generator after v1's rotation-sensitivity surfaced; 14+17 pinned,
two-run verified). B3 ✓ by the letter (1 repair closure) with the
honest reading recorded: zero marginal over symbolic, and 10 of 39
calls lost to thinking-block extraction — the client gap the
transcripts (B4 ✓, entry-for-entry) were built to catch. B5 ✓ (full
suite green). See REPORT_BENCH.md.

## The two prongs, in order

Witness kits first (deterministic, free), the repair rung second (live,
budgeted) — so LLM calls are spent only on statements that survived a
serious refutation attempt.

## Decisions

**K1 — Richer matroid witnesses.** The current kit's six witnesses have
no rank structure above 1, which is why the `dual_IsRkFinite` family
sits unrefuted. Add witnesses with real structure — a two-element free
matroid, a two-element loopy matroid, and a uniform matroid
(`Matroid.unifOn`-style) if its characterization lemmas cooperate —
with their simp vocabulary, in the established kit pattern
(hand-proved characterizations at the witness where the library's
conditional lemmas need discharging). The memo pre-registers the
*target* (claim B1), not the exact witness list: kits are tuned
empirically, run-look-adjust, as the original kit was.

**K2 — Structured graph witnesses.** `⊥`/`⊤` cannot separate anything
that needs an actual edge pattern. Add one or two concrete graphs on ℕ
(`SimpleGraph.fromRel` definitions — a path, a single edge) with
hand-proved adjacency characterization simp lemmas, same pattern.

**K3 — Kits change the generator, so the corpus version bumps.** Richer
in-loop refuters mean fewer opens at generation time: corpus v2, new
pins, loudly. The v1 → v2 delta in opens, all kernel-certified
refutations, *is* prong 1's measurement.

**K4 — Repair over the v2 survivors** (`BenchProveRun.lean`, live):
the repair rung, two calls per statement, transcripts on (their first
real workout), every closure through the gate at the escalated tier.
Budget ≈ 2 × |survivors| ≤ ~40 Bedrock calls.

**K5 — Out of scope**: the stepper on the benchmark (its first
comparison was null; revisit only with domain move sets), embedding
retrieval, new prover rungs, the paper.

## Pre-registered claims

- **B1**: the enriched kits certifiably refute ≥ 3 statements of the
  v1 residue (visible as the v1 → v2 open-count drop, each refutation
  a kernel-gated negated instance).
- **B2**: the corpus version bumps loudly — v2 pins asserted, version
  field updated, REPORT_BENCH records both baselines.
- **B3**: repair closes ≥ 1 v2 survivor (zero is the finding, reported
  as such — the arc's precedent).
- **B4**: the transcript file's entry count equals the calls made —
  R1's machinery verified in live use.
- **B5**: no regression — the kits are additive; the full CI suite and
  the existing matroid/graph runs pass unchanged (kit-consuming runs
  may see *more* refutations, which their ≥-style assertions absorb).

## Sequence

1. K1 + K2 (kit enrichment) → rerun `BenchRun` → v2 pins + B1/B2.
2. K4 (`BenchProveRun.lean`) → B3/B4.
3. `REPORT_BENCH.md` v2 section; suite sweep (B5).
