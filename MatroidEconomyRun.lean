import EurekaMathlib

/-!
The starvation experiment. Three prior runs observed the same finding: in
a refuter-free domain, a template agent is killed by the worth economics
with its provable conjectures still queued behind a false-heavy
enumeration prefix. None of them could ask the follow-up — does a live
refuter change the agent's fate? — because refuted and open were
indistinguishable.

Here the same `exclusions` agent runs through the same population engine
twice: once refuter-free (the control, reproducing the documented kill),
once with the matroid refuter wired into `judge`. The worth function pays
admissions only, so the hypothesis is that certified refutations change
the *diagnosis* (the agent's failures become provably-false rather than
maybe-just-hard) but not the *verdict* (the kill) — if so, starvation is a
property of the admissions-only worth function, and repricing worth is
exactly the reflective-modification question one gate up (lean-keep's
axis). Deterministic; no LLM. Run with
`lake env lean MatroidEconomyRun.lean` (not in CI: needs the Mathlib
build).
-/

open Lean Eureka.Runtime

set_option linter.unusedSimpArgs false

def runOnce (refuterOn : Bool) : MetaM (Nat × Nat) := do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let pool := preds.toList.take 10 |>.toArray
  let cfg : EvolveConfig := {
    knownPrefixes := [carrier]
    refuter := if refuterOn then matroidRefuter else fun _ => pure none }
  let corpus ← evolve [exclusionsAgent carrier pool] cfg
  let neg := corpus.facts.filter fun f => f.name.toString.endsWith "_refuted"
  IO.println s!"corpus: {corpus.facts.size} facts \
({corpus.facts.size - neg.size} admissions + {neg.size} certified refutations)"
  return (corpus.facts.size - neg.size, neg.size)

#eval show MetaM Unit from do
  IO.println "═══ control: refuter off ═══"
  let (adm₀, ref₀) ← runOnce false
  IO.println ""
  IO.println "═══ experiment: refuter on ═══"
  let (adm₁, ref₁) ← runOnce true
  IO.println ""
  IO.println s!"control: {adm₀} admitted, {ref₀} refutations; \
experiment: {adm₁} admitted, {ref₁} refutations"
  unless ref₀ == 0 do
    throwError "control must be refuter-free, got {ref₀} refutations"
  unless ref₁ > 0 do
    throwError "experiment expected certified refutations, got none"
