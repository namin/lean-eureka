import EurekaMathlib

/-!
The matroid microcosm. The user supplies one name — `Matroid` — and the
system extracts the namespace's predicates by signature shape, maps their
implication structure with kernel-certified edges, and probes invented
predicates (taken from the actual formal-disco matroid run's synonym tower)
for certified aliases. No seed file, no curated canonical pool.

There is no counterexample search in this domain, so non-theorems are
reported open, not refuted — the honest asymmetry.
Run with `lake env lean MatroidStub.lean` (not in CI: needs the Mathlib
build).
-/

open Lean Eureka.Runtime

/-- `is_loop_def` from the formal-disco matroid run: the invented loop
predicate that aliased `Matroid.IsLoop` (REPORT_ALIGN's synonym tower). -/
def is_loop_def {α : Type} (M : Matroid α) (e : α) : Prop :=
  e ∈ M.E ∧ ¬ M.Indep {e}

/-- An invented dependence predicate: `Matroid.Dep` with the conjuncts
swapped — not definitionally equal, needs propositional reasoning. -/
def dep_invented {α : Type} (M : Matroid α) (X : Set α) : Prop :=
  X ⊆ M.E ∧ ¬ M.Indep X

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  IO.println s!"{preds.size} predicates extracted from the {carrier} namespace:"
  for p in preds do
    let shape := if p.shape == PredShape.element then "element" else "set"
    IO.println s!"  {p.name} ({shape})"
  -- Cap the sweep pool; say so (no silent caps).
  let pool := preds.toList.take 10 |>.toArray
  if pool.size < preds.size then
    IO.println s!"sweep pool capped at {pool.size} of {preds.size}"
  let known ← collectKnown [carrier]
  IO.println s!"grounding pool: {known.size} {carrier}.* lemmas"
  IO.println ""
  IO.println "── implication sweep ──"
  let (corpus, admitted, opens) ← implicationSweep known carrier pool {}
  IO.println s!"  ({opens.size} candidate implications remain open — no refuter in this domain)"
  IO.println ""
  IO.println "── alias probes (the synonym tower, in-process) ──"
  let mut corpus := corpus
  for (invented, shape) in [(``is_loop_def, PredShape.element),
                            (``dep_invented, PredShape.set)] do
    let (corpus', grounding) ← aliasProbe known carrier shape invented pool corpus
    corpus := corpus'
    match grounding with
    | some (canonical, note) =>
      IO.println s!"  ✓ {invented} is {canonical} ({note})"
    | none =>
      IO.println s!"  ? {invented}: no alias certified among the pool"
  IO.println ""
  IO.println s!"corpus: {corpus.facts.size} kernel-certified facts \
({admitted} implication edges + alias certificates)"
  unless admitted ≥ 2 do
    throwError "expected at least 2 certified implication edges, got {admitted}"
  unless corpus.facts.size > admitted do
    throwError "expected at least one certified alias"
  IO.println "matroid microcosm behaves as specified"
