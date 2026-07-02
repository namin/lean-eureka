import EurekaMathlib

/-!
The frontier harvest: a *complete* sweep of the exclusion family
(`P X → ¬ Q X`) over the extracted `Matroid` predicates, with the
composition rung active. Facts admitted with a `composed:` certificate are
the yield — true, kernel-certified, and unmatched by the grounding pass
over the `Matroid.*` pool (grounding is tried first and finds no alias;
not an exhaustive search of Mathlib).
Deterministic; no LLM. A sweep rather than the budgeted agenda: for a
completeness question, economics are the wrong tool.
Run with `lake env lean MatroidFrontierRun.lean`.
-/

open Lean Eureka.Runtime

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let pool := preds.toList.take 10 |>.toArray
  IO.println s!"predicate pool: {pool.size} of {preds.size} extracted"
  let known ← collectKnown [carrier]
  let mut corpus : Corpus := {}
  let mut grounded := 0
  let mut composed := 0
  let mut opens := 0
  for P in pool do
    for Q in pool do
      if P.name != Q.name && P.shape == Q.shape then
        let stmt ← mkPredForall carrier P.shape fun M X => do
          Lean.mkArrow (← Lean.Meta.mkAppM P.name #[M, X])
            (Lean.mkNot (← Lean.Meta.mkAppM Q.name #[M, X]))
        let c : Conjecture :=
          { name := .mkSimple s!"{P.name.getString!}_excl_{Q.name.getString!}",
            stmt, origin := `exclusions }
        let (corpus', outcome) ← judge known corpus c
        corpus := corpus'
        match outcome with
        | .admitted _ note =>
          if note.startsWith "composed" then composed := composed + 1
          else grounded := grounded + 1
          IO.println s!"  ✓ {toString (← Meta.ppExpr c.stmt)} — {note}"
        | .stillOpen => opens := opens + 1
        | .refuted cex =>
          IO.println s!"  ✗ {toString (← Meta.ppExpr c.stmt)} — refuted ({cex})"
        | .refusedAtGate =>
          IO.println s!"  ! {toString (← Meta.ppExpr c.stmt)} — REFUSED"
  IO.println ""
  IO.println s!"exclusion sweep: {grounded} grounded, {composed} composed \
(kernel-certified, unmatched by the grounding pass), {opens} open"
