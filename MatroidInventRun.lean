import EurekaMathlib

/-!
The concept booth against a live LLM (DESIGN_INVENT D6): Claude on
Bedrock proposes matroid predicate *definitions*; the birth gate and the
identity probes judge them. The interesting question is the split: how
much of what the model invents is existing vocabulary in disguise
(merged at birth with a certificate — the synonym tower, strangled in
the crib), how much is degenerate, and how much survives as genuinely
novel and earns certified edges.

Requires the `aws` CLI with Bedrock access; everything the model returns
is untrusted and passes through the same gate as the template operators.
Run with `lake env lean MatroidInventRun.lean` (not in CI: live LLM +
Mathlib build).
-/

open Lean Meta Eureka.Runtime

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let mut canonical : Array ProbeTarget := #[]
  for p in preds do
    if let some t ← probeTargetOfConst p.name then
      canonical := canonical.push t
  IO.println s!"{canonical.size} canonical predicates extracted from {carrier}"
  let known ← collectKnown [carrier]
  IO.println s!"grounding pool: {known.size} {carrier}.* lemmas"
  let ctx : ProbeCtx :=
    { known
      extraRungs := #["tauto", "aesop",
        "simp only [Matroid.dep_iff, Matroid.IsColoop, Matroid.dual_dual, \
Matroid.singleton_dep, Set.singleton_subset_iff, and_comm, and_assoc, \
and_left_comm]"] }
  let elemTy ← withLocalDeclD `α (mkSort (.succ .zero)) fun α =>
    withLocalDeclD `M (mkApp (mkConst `Matroid [.zero]) α) fun M =>
      withLocalDeclD `e α fun e =>
        mkForallFVars #[α, M, e] (.sort .zero)
  let setTy ← withLocalDeclD `α (mkSort (.succ .zero)) fun α =>
    withLocalDeclD `M (mkApp (mkConst `Matroid [.zero]) α) fun M =>
      withLocalDeclD `X (mkApp (mkConst ``Set [.zero]) α) fun X =>
        mkForallFVars #[α, M, X] (.sort .zero)
  let shapes : Array ConceptShape :=
    #[⟨"element", "(α : Type) (M : Matroid α) (e : α)", elemTy⟩,
      ⟨"set", "(α : Type) (M : Matroid α) (X : Set α)", setTy⟩]
  let domain := "matroids, via Mathlib's `Matroid α` (ground set `M.E : Set α`, \
independence `M.Indep : Set α → Prop`, dual `M✶`). In bodies use only the \
Mathlib matroid API (e.g. `M.E`, `M.Indep`, `M.Dep`, `M.IsBase`, \
`M.IsCircuit`, `M.IsLoop`, `M.Spanning`, `M✶`, `M.closure`) and set \
operations (`∈`, `⊆`, `∩`, `∪`, `\\`, `{e}`, `Set.Finite`)"
  let (pool, corpus, stats) ← conceptBooth
    (Eureka.LLM.invoke Eureka.LLM.defaultConfig) ctx canonical
    { rounds := 2, perRound := 4, shapes
      render := renderConceptPrompt domain shapes }
  IO.println ""
  IO.println s!"  {stats.describe}"
  IO.println ""
  IO.println s!"pool: {pool.concepts.size} born, {pool.live.size} live"
  for c in pool.concepts do
    match c.mergedInto with
    | some t => IO.println s!"  ≡ {c.name} → {t}"
    | none =>
      IO.println s!"  ✦ {c.name} (novel-so-far)"
      IO.println s!"      := {toString (← ppExpr c.value)}"
  IO.println ""
  IO.println s!"corpus: {corpus.facts.size} kernel-certified facts:"
  for f in corpus.facts do
    IO.println s!"  {f.name} : {toString (← ppExpr f.stmt)}"
  unless (← auditInvented pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
