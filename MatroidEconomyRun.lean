import EurekaMathlib

/-!
The starvation experiment, re-run under the ledger economy
(DESIGN_WORTH acceptance test 1).

The original finding (three runs over): with admissions-only worth, the
`exclusions` agent's fate was *identical* with the refuter off and on —
18 open vs 17 certified-refuted + 1 open, same agenda, same death.
Certified refutations were economically invisible, and repricing worth
was flagged as the reflective-modification question one gate up.

That gate has now been built (`Eureka/Worth.lean`): worth is a fold of
the event ledger through the pricing table, and refutations pay with
decaying returns. The experiment's demand flips from diagnosis to
regression: the same agent, same domain, refuter off vs on — the worth
trajectories must now *separate*, with the refuted-heavy run strictly
above the open-heavy control. Deterministic; no LLM. Run with
`lake env lean MatroidEconomyRun.lean` (not in CI: needs the Mathlib
build).
-/

open Lean Eureka.Runtime

set_option linter.unusedSimpArgs false

def runOnce (refuterOn : Bool) : MetaM (Nat × Nat × Float) := do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let pool := preds.toList.take 10 |>.toArray
  let cfg : EvolveConfig := {
    knownPrefixes := [carrier]
    refuter := if refuterOn then matroidRefuter else fun _ => pure none }
  let r ← evolveWith [exclusionsAgent carrier pool] cfg
  let neg := r.corpus.facts.filter fun f => f.name.toString.endsWith "_refuted"
  let w := r.ledger.worth {} (fun _ => #[]) `exclusions
  IO.println s!"corpus: {r.corpus.facts.size} facts \
({r.corpus.facts.size - neg.size} admissions + {neg.size} certified \
refutations); exclusions worth {w}"
  return (r.corpus.facts.size - neg.size, neg.size, w)

#eval show MetaM Unit from do
  IO.println "═══ control: refuter off ═══"
  let (adm₀, ref₀, w₀) ← runOnce false
  IO.println ""
  IO.println "═══ experiment: refuter on ═══"
  let (adm₁, ref₁, w₁) ← runOnce true
  IO.println ""
  IO.println s!"control: {adm₀} admitted, {ref₀} refutations, worth {w₀}; \
experiment: {adm₁} admitted, {ref₁} refutations, worth {w₁}"
  unless ref₀ == 0 do
    throwError "control must be refuter-free, got {ref₀} refutations"
  unless ref₁ > 0 do
    throwError "experiment expected certified refutations, got none"
  unless w₁ > w₀ do
    throwError "refutations must pay: the trajectories should separate \
(worth on {w₁} ≤ off {w₀})"
  IO.println "the economy sees refutations; the trajectories separated"
