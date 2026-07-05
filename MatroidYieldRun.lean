import EurekaMathlib

/-!
# The yield curve, slice one (DESIGN_INVENT D5)

The fixed operator set — dualization, singleton-lift, conjunction,
negated-conjunct — applied *exhaustively* over the predicates extracted
from the `Matroid` namespace, every product pushed through the concept
lifecycle. The metrics were fixed in the design before any code:
candidates, refused, degenerate, alias-at-birth, novel survivors — per
operator — then a facts phase over the survivors (implications against
the canonical pool, judged with the matroid refuter) for facts earned
and the refuted-conjecture rate. The AM post-mortem's yield-decay claim
becomes this table; every cell is kernel-certified.

Economy — configured, logged, never silent:
* probe attempts run under a reduced heartbeat budget
  (`probeHeartbeats := 2000`): the cheap rungs (refl, permuted simp,
  chain) decide well under it; what only a curtailed heavy rung would
  have certified stays novel-so-far, re-probeable under D3;
* birth probes are alias-only (`probeEdges := false`) — edges are
  measured once, in the facts phase, with the refuter;
* newborns are alias-probed against the canonical pool plus the 12 most
  recent inventions (`inventedTargetWindow`); the older tail belongs to
  the budgeted sweep, which is D3's design, not a cap.

Progress streams to `yield-progress.log` in the working directory
(Lean buffers `#eval` output until the command ends; the file is the
live view). Deterministic (no LLM). Run with
`lake env lean MatroidYieldRun.lean` (not in CI: needs the Mathlib
build).
-/

open Lean Meta Eureka.Runtime

def progressPath : System.FilePath := "yield-progress.log"

def note (s : String) : IO Unit := do
  IO.FS.withFile progressPath .append fun h => h.putStrLn s

def addStats (a b : InventStats) : InventStats :=
  { candidates := a.candidates + b.candidates
    refused := a.refused + b.refused
    degenerate := a.degenerate + b.degenerate
    aliased := a.aliased + b.aliased
    novel := a.novel + b.novel
    edgeFacts := a.edgeFacts + b.edgeFacts }

set_option linter.unusedSimpArgs false in
#eval show MetaM Unit from do
  IO.FS.writeFile progressPath ""
  let carrier := `Matroid
  let preds ← collectPredicates carrier
  let mut canonical : Array ProbeTarget := #[]
  for p in preds do
    if let some t ← probeTargetOfConst p.name then
      canonical := canonical.push t
  let known ← collectKnown [carrier]
  let policy := s!"{canonical.size} canonical predicates, grounding pool \
{known.size} lemmas; probe budget 2000 heartbeats/attempt, alias-only at \
birth (edges in the facts phase), invented-target window 12 (tail → sweep)"
  IO.println policy
  note policy
  let ctx : ProbeCtx :=
    { known
      extraRungs := #["tauto",
        "simp only [Matroid.dep_iff, Matroid.IsColoop, Matroid.dual_dual, \
Matroid.singleton_dep, Set.singleton_subset_iff, and_comm, and_assoc, \
and_left_comm]"]
      probeHeartbeats := some 2000
      probeEdges := false
      inventedTargetWindow := some 12 }
  -- Depth-1 enumeration, per operator; the pool carries over, so later
  -- products are probed against earlier survivors (within the window).
  let mut batches : Array (String × Array ConceptProposal) := #[]
  let mut ps : Array ConceptProposal := #[]
  for t in canonical do
    if let some p ← mkDualizeProposal t then ps := ps.push p
  batches := batches.push ("dualize", ps)
  ps := #[]
  for t in canonical do
    if let some p ← mkSingletonLiftProposal t then ps := ps.push p
  batches := batches.push ("singleton-lift", ps)
  ps := #[]
  for i in [0 : canonical.size] do
    for j in [i + 1 : canonical.size] do
      if let some p ← mkConjProposal false canonical[i]! canonical[j]! then
        ps := ps.push p
  batches := batches.push ("conjunction", ps)
  ps := #[]
  for i in [0 : canonical.size] do
    for j in [0 : canonical.size] do
      if i != j then
        if let some p ← mkConjProposal true canonical[i]! canonical[j]! then
          ps := ps.push p
  batches := batches.push ("negated-conjunct", ps)
  let total := batches.foldl (fun n (_, b) => n + b.size) 0
  note s!"{total} candidates enumerated"

  let mut pool : ConceptPool := {}
  let mut corpus : Corpus := {}
  let mut table : Array (String × InventStats) := #[]
  let mut done := 0
  for (opName, batch) in batches do
    IO.println ""
    IO.println s!"━━ operator: {opName} — {batch.size} candidates ━━"
    let mut stats : InventStats := {}
    for p in batch do
      let (pool', corpus', s, reports) ←
        inventRoundWith ctx pool corpus canonical #[p]
      pool := pool'
      corpus := corpus'
      stats := addStats stats s
      done := done + 1
      let fate := match reports[0]? with
        | some r => match r.outcome with
          | .error e => s!"refused: {e}"
          | .ok v => v.describe
        | none => "?"
      note s!"[{done}/{total}] {opName} {p.name} — {fate}"
    table := table.push (opName, stats)

  -- Facts phase: survivor × canonical implications, both directions.
  -- The prover is `probeProve` — it delta-expands invented vocabulary,
  -- where `judge`'s hunt would see opaque constants. The refuter gets the
  -- survivors' definitions added to its simp vocabulary so it can
  -- evaluate invented predicates at the witnesses. A refutation is a
  -- kernel fact (the negated instance), committed through the gate.
  IO.println ""
  IO.println "━━ facts phase: survivor × canonical implications, with refuter ━━"
  let survivors := pool.live
  note s!"facts phase: {survivors.size} survivors × canonical, both \
directions (survivor × survivor deferred to the next sweep)"
  let factsCtx := { ctx with probeHeartbeats := some 5000 }
  -- The refuter gets *targeted* unfolds — just the invented names the
  -- statement mentions, not the whole pool: a 100-entry simp vocabulary
  -- under a budget is curtailed into silence before it decides anything.
  let refCtx := { ctx with probeHeartbeats := some 20000 }
  let mut attempted := 0
  let mut admitted := 0
  let mut refuted := 0
  let mut opens := 0
  for c in survivors do
    for t in canonical do
      unless ← targetsCompatible c.toTarget t do continue
      for (a, b) in [(c.toTarget, t), (t, c.toTarget)] do
        let some stmt ← mkImplStmt a b | continue
        if corpus.facts.any (·.stmt == stmt) then continue
        attempted := attempted + 1
        let base := s!"{a.name.getString!}_imp_{b.name.getString!}"
        -- simp cannot unfold gate-declared defs (no equation lemmas for
        -- raw `addDecl`); `unfold` can — prefix it.
        let usedInvented := (stmt.getUsedConstants.filter
          (inventedNs.isPrefixOf ·)).map toString
        let pre := s!"unfold {String.intercalate " " usedInvented.toList}; "
        let refuter : Refuter := fun s => refuteByInstances
          matroidRefuterSimpArgs (mkConst ``Nat) matroidInstances s (pre := pre)
        if let some (negStmt, pf, witness) ← refCtx.withBudget <|
            withCurrHeartbeats <| refuter stmt then
          let nm ← freshName (.mkSimple s!"{base}_refuted")
          if let some f ← commitFact { name := nm, stmt := negStmt, proof := pf } then
            corpus := { corpus with facts := corpus.facts.push f }
            refuted := refuted + 1
            IO.println s!"  ✗ {toString (← ppExpr stmt)} — refuted ({witness})"
          else
            opens := opens + 1
        else if let some (pf, how) ← factsCtx.withBudget <|
            withCurrHeartbeats <| probeProve factsCtx corpus stmt then
          if let some (corpus', _) ← commitProbeFact corpus base stmt pf then
            corpus := corpus'
            admitted := admitted + 1
            IO.println s!"  ✓ {toString (← ppExpr stmt)} — admitted ({how})"
          else
            opens := opens + 1
        else
          opens := opens + 1
        if attempted % 25 == 0 then
          note s!"facts: {attempted} judged, {admitted} admitted, \
{refuted} refuted, {opens} open"

  IO.println ""
  IO.println "━━ the yield table (slice one, generative depth 1) ━━"
  let mut summary := "yield table:\n"
  for (opName, s) in table do
    summary := summary ++ s!"  {opName}: {s.describe}\n"
  summary := summary ++ s!"  facts phase: {attempted} implications judged — \
{admitted} admitted, {refuted} refuted (certified, via the witness kit), \
{opens} open\n"
  summary := summary ++ s!"  pool: {pool.concepts.size} born, \
{survivors.size} novel survivors; corpus: {corpus.facts.size} \
kernel-certified facts"
  IO.println summary
  note summary
  unless (← auditInvented pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  IO.println ""
  IO.println "yield curve, slice one: measured"
  note "yield curve, slice one: measured"
