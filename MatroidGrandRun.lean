import EurekaMathlib

/-!
# The grand run (DESIGN_INVENT C5, acceptance test S4)

Everything in one population, on the matroid domain: the template fact
agents (implications, exclusions, duality, singleton bridges), the
dualization operator and the compounding agent (depth-2 products), the
invented-implications agent (which makes invention *pay* — its
admissions credit the concepts' inventors), and the LLM concept booth
as a population member — all under the repriced economy, the
invented-aware refuter, re-probe trigger (i), and the exploration
floor. Every admission through the gates; worth only schedules.

Requires the `aws` CLI with Bedrock access (one model call per
generation for the booth). Run with
`lake env lean MatroidGrandRun.lean` (not in CI: live LLM + Mathlib).
-/

open Lean Meta Eureka.Runtime

set_option linter.unusedSimpArgs false

#eval show MetaM Unit from do
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let mut canonical : Array ProbeTarget := #[]
  for p in preds do
    if let some t ← probeTargetOfConst p.name then
      canonical := canonical.push t
  let known ← collectKnown [carrier]
  IO.println s!"{canonical.size} canonical predicates, {known.size} lemmas"
  let ctx : ProbeCtx :=
    { known
      extraRungs := #["tauto",
        "simp only [Matroid.dep_iff, Matroid.IsColoop, Matroid.dual_dual, \
Matroid.singleton_dep, Set.singleton_subset_iff, and_comm, and_assoc, \
and_left_comm]"]
      probeHeartbeats := some 5000
      probeEdges := false
      inventedTargetWindow := some 12 }
  -- The refuter, invented-aware: unfold-prefixed when the statement
  -- mentions invented vocabulary (simp cannot unfold gate-declared defs).
  let refuter : Refuter := fun stmt => do
    let usedInv := (stmt.getUsedConstants.filter
      (inventedNs.isPrefixOf ·)).map toString
    let pre := if usedInv.isEmpty then "" else
      s!"unfold {String.intercalate " " usedInv.toList}; "
    refuteByInstances matroidRefuterSimpArgs (mkConst ``Nat)
      matroidInstances stmt (pre := pre)
  -- The LLM concept booth as an agent.
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
  let booth := conceptBoothAgent
    (Eureka.LLM.invoke Eureka.LLM.defaultConfig) shapes domain canonical
  let agents : List Agent :=
    [implicationsAgent carrier preds, exclusionsAgent carrier preds,
     dualityAgent preds, singletonAgent preds,
     dualizerAgent canonical, compounderAgent,
     inventedImplAgent canonical, booth]
  let r ← evolveWith agents
    { generations := 4, judgeBudget := 40, perAgentCap := 20,
      knownPrefixes := [carrier], refuter, probeCtx := some ctx, canonical }
  -- The instruments.
  IO.println ""
  IO.println "── the pool, by depth ──"
  let mut d1 := (0, 0)  -- (certified: alias/degenerate, novel)
  let mut d2 := (0, 0)
  for c in r.pool.concepts do
    let cert := c.mergedInto.isSome
    if c.depth == 1 then d1 := if cert then (d1.1 + 1, d1.2) else (d1.1, d1.2 + 1)
    else d2 := if cert then (d2.1 + 1, d2.2) else (d2.1, d2.2 + 1)
    let fate := match c.mergedInto with
      | some t => s!"≡ {t}"
      | none => "✦ live"
    IO.println s!"  d{c.depth} {c.name} [{c.origin}] {fate}"
  IO.println s!"  depth 1: {d1.1} certified, {d1.2} novel-so-far; \
depth 2: {d2.1} certified, {d2.2} novel-so-far"
  let inventedFacts := r.corpus.facts.filter fun f =>
    f.stmt.getUsedConstants.any (inventedNs.isPrefixOf ·)
  IO.println ""
  IO.println s!"corpus: {r.corpus.facts.size} kernel-certified facts, \
{inventedFacts.size} in invented vocabulary"
  for f in inventedFacts do
    IO.println s!"  {f.name} : {toString (← ppExpr f.stmt)}"
  -- S4 assertions.
  let bc := r.ledger.counts `concept_booth
  unless bc.conceptsNovel + bc.conceptsAliased + bc.conceptsDegenerate +
      bc.conceptsRefused ≥ 1 do
    throwError "expected at least one LLM-proposed concept judged"
  unless (← auditInvented r.pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  IO.println ""
  IO.println "the grand run: complete, audit clean (S4)"
