import EurekaMathlib

/-!
# The omega run: everything, on the second carrier

The first run in which every capability the project has built operates
simultaneously: the LLM concept booth inventing graph vocabulary, the
complement operator and its compounder (depth-capped, alias-decayed),
the invented-implications agent, the full ledger economy (tiers,
attracted credit, the floor), escalation with a graph deep ladder
(safe canonical transparency, `Set` lemmas, composition depth 3), the
LLM repair rung *inside* the population, and the graph witness kit's
refuter — on `SimpleGraph`, the carrier none of this code grew up on.

Open questions it instruments: does the booth restate against a sparse
canonical pool (five predicates — restatement pressure far higher than
matroids), and does the repair rung close an invented-vocabulary
implication in vivo — which would be the first LLM-proved fact inside a
discovery run rather than a bench harness.

Live LLM (≈ 10–16 Bedrock calls) + Mathlib; not in CI. Run with
`lake env lean GraphGrandRun.lean`.
-/

open Lean Meta Eureka.Runtime

set_option linter.unusedSimpArgs false

#eval show MetaM Unit from do
  let carrier := `SimpleGraph
  let preds ← collectPredicates carrier
  let mut canonical : Array ProbeTarget := #[]
  for p in preds do
    if let some t ← probeTargetOfConst p.name then
      canonical := canonical.push t
  let known ← collectKnown [carrier]
  IO.println s!"{canonical.size} canonical predicates, {known.size} lemmas"
  let cheapRungs : Array String := #["tauto",
    "simp only [SimpleGraph.isClique_compl, SimpleGraph.isIndepSet_compl, \
SimpleGraph.isClique_iff, SimpleGraph.isIndepSet_iff, compl_compl, \
and_comm, and_assoc, and_left_comm]"]
  let ctx : ProbeCtx :=
    { known, extraRungs := cheapRungs
      probeHeartbeats := some 5000
      probeEdges := false
      inventedTargetWindow := some 12 }
  let deepKnown ← collectKnown [carrier, `Set]
  let mut safeCanon : Array Name := #[]
  for t in canonical do
    if let some ci := (← getEnv).find? t.name then
      if let some v := ci.value? then
        let mut b := v
        while b.isLambda do
          b := b.bindingBody!
        if b.getAppFn.isConst then
          safeCanon := safeCanon.push t.name
  let safeCanon' := safeCanon
  let deepCtx : ProbeCtx :=
    { known := deepKnown
      transparent := fun n =>
        inventedNs.isPrefixOf n || safeCanon'.contains n
      extraRungs := cheapRungs ++ #["aesop"]
      composeDepth := 3 }
  -- the booth, in graph clothes
  let elemTy ← withLocalDeclD `α (mkSort (.succ .zero)) fun α =>
    withLocalDeclD `G (mkApp (mkConst `SimpleGraph [.zero]) α) fun G =>
      withLocalDeclD `v α fun v =>
        mkForallFVars #[α, G, v] (.sort .zero)
  let setTy ← withLocalDeclD `α (mkSort (.succ .zero)) fun α =>
    withLocalDeclD `G (mkApp (mkConst `SimpleGraph [.zero]) α) fun G =>
      withLocalDeclD `X (mkApp (mkConst ``Set [.zero]) α) fun X =>
        mkForallFVars #[α, G, X] (.sort .zero)
  let shapes : Array ConceptShape :=
    #[⟨"element", "(α : Type) (G : SimpleGraph α) (v : α)", elemTy⟩,
      ⟨"set", "(α : Type) (G : SimpleGraph α) (X : Set α)", setTy⟩]
  let domain := "simple graphs, via Mathlib's `SimpleGraph α` (adjacency \
`G.Adj : α → α → Prop`, complement `Gᶜ`, neighborhoods `G.neighborSet v`). \
In bodies use only the Mathlib graph API (e.g. `G.Adj`, `Gᶜ`, \
`G.IsClique`, `G.IsIndepSet`, `G.neighborSet`, `G.degree` needs \
instances — avoid it) and set operations (`∈`, `⊆`, `∩`, `∪`, `\\`, \
`{v}`, `Set.univ`)"
  let call ← Eureka.LLM.withTranscript "transcripts/graph-grand.jsonl" "graph-grand"
    (Eureka.LLM.invoke Eureka.LLM.defaultConfig)
  let booth := conceptBoothAgent call shapes domain canonical
  let agents : List Agent :=
    [complementerAgent canonical, graphCompounderAgent,
     inventedImplAgent canonical, booth]
  let r ← evolveWith agents
    { generations := 4, judgeBudget := 30, perAgentCap := 20,
      knownPrefixes := [carrier], refuter := graphRefuter,
      probeCtx := some ctx, canonical,
      escalationBudget := 5, deepCtx := some deepCtx,
      proofCall := some call, llmProofBudget := 1 }
  IO.println ""
  IO.println "── the pool, by depth ──"
  for c in r.pool.concepts do
    let fate := match c.mergedInto with
      | some t => s!"≡ {t}"
      | none => "✦ live"
    IO.println s!"  d{c.depth} {c.name} [{c.origin}] {fate}"
  let inventedFacts := r.corpus.facts.filter fun f =>
    f.stmt.getUsedConstants.any (inventedNs.isPrefixOf ·)
  IO.println ""
  IO.println s!"corpus: {r.corpus.facts.size} kernel-certified facts, \
{inventedFacts.size} in invented vocabulary"
  for f in inventedFacts do
    IO.println s!"  {f.name} : {toString (← ppExpr f.stmt)}"
  let repairWins := r.ledger.events.filter fun e =>
    e.kind == .factAdmitted .escalated
  IO.println s!"escalated-tier admissions (symbolic + llm-repair): \
{repairWins.size}"
  let bc := r.ledger.counts `concept_booth
  unless bc.conceptsNovel + bc.conceptsAliased + bc.conceptsDegenerate +
      bc.conceptsRefused ≥ 1 do
    throwError "expected at least one LLM-proposed concept judged"
  unless (← auditInvented r.pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  IO.println ""
  IO.println "the omega run: complete, audit clean"
