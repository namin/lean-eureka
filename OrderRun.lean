import EurekaMathlib

/-!
The third-carrier run: the whole stack on Boolean algebras — the first
*instance-shaped* domain. Pre-registered claims, rhyming with
DESIGN_GRAPH's:

1. **Extraction + canonicalization generalize**: the root scan finds the
   element-shaped instance predicates, and elaboration over the ambient
   class canonicalizes (at least) `IsAtom`, `IsCoatom`, `SupIrred`,
   `InfIrred` into the uniform carrier type — with no hand-curated list.
2. **The involution grounds at birth**: `compl_IsAtom ≡ BA.IsCoatom` and
   `compl_IsCoatom ≡ BA.IsAtom`, certified (the library bridge is
   `isAtom_compl` — the analog of `isClique_compl`).
3. **Compounding rhymes**: a depth-2 `compl_compl_P` merges back into
   canonical `BA.P` (the involution, as `dual_dual_Dep ≡ Dep`).
4. **The refuter generalizes**: the Bool/Bool² kit certifies at least
   one refutation of a false invented-vocabulary implication.
5. **The economy carries over**: the complementer earns certified
   aliases; audit clean.

Deterministic; no LLM. Run with `lake env lean OrderRun.lean` (not in
CI: needs the Mathlib build).
-/

open Lean Meta Eureka.Runtime

set_option linter.unusedSimpArgs false

#eval show MetaM Unit from do
  -- ── claim 1: extraction + canonicalization ──
  let raws ← rootInstancePredicates
  IO.println s!"root scan: {raws.size} element-shaped instance predicates"
  let mut canonical : Array ProbeTarget := #[]
  let mut rawNames : Array Name := #[]
  for n in raws do
    if let some t ← canonicalizeOrderPredicate n then
      canonical := canonical.push t
      rawNames := rawNames.push n
  IO.println s!"claim 1 — canonicalized over BooleanAlgebra: \
{canonical.size} predicates:"
  for t in canonical do
    IO.println s!"  {t.name}"
  for expected in [`BA.IsAtom, `BA.IsCoatom, `BA.SupIrred, `BA.InfIrred] do
    unless canonical.any (·.name == expected) do
      throwError "claim 1: expected {expected} in the canonical pool"
  let known ← collectKnownMentioning rawNames
  IO.println s!"grounding pool: {known.size} lemmas mentioning the raw \
predicates"
  -- ── the run ──
  let cheapRungs : Array String := #["tauto",
    "simp only [isAtom_compl, isCoatom_compl, compl_compl, compl_top, \
compl_bot, and_comm, and_assoc, and_left_comm]"]
  let transparent := fun n =>
    inventedNs.isPrefixOf n || baNs.isPrefixOf n
  let ctx : ProbeCtx :=
    { known, extraRungs := cheapRungs, transparent
      probeHeartbeats := some 5000
      probeEdges := false
      inventedTargetWindow := some 12 }
  let deepCtx : ProbeCtx :=
    { known, extraRungs := cheapRungs ++ #["aesop"], transparent
      composeDepth := 3 }
  let r ← evolveWith
    [orderComplementerAgent canonical, orderCompounderAgent,
     inventedImplAgent canonical]
    { generations := 3, judgeBudget := 20, perAgentCap := 20,
      knownPrefixes := [`BooleanAlgebra, `Bool],
      refuter := orderRefuter, probeCtx := some ctx, canonical,
      escalationBudget := 5, deepCtx := some deepCtx }
  IO.println ""
  IO.println "── the pool ──"
  for c in r.pool.concepts do
    let fate := match c.mergedInto with
      | some t => s!"≡ {t}"
      | none => "✦ live"
    IO.println s!"  d{c.depth} {c.name} [{c.origin}] {fate}"
  -- ── claim 2: the involution grounds at birth ──
  let mergedInto := fun (base : Name) =>
    (r.pool.find? (inventedNs ++ base)).bind (·.mergedInto)
  unless mergedInto `compl_IsAtom == some `BA.IsCoatom do
    throwError "claim 2: compl_IsAtom should merge into BA.IsCoatom, \
got {mergedInto `compl_IsAtom}"
  unless mergedInto `compl_IsCoatom == some `BA.IsAtom do
    throwError "claim 2: compl_IsCoatom should merge into BA.IsAtom, \
got {mergedInto `compl_IsCoatom}"
  -- ── claim 3: a depth-2 involution product merges back ──
  unless r.pool.concepts.any (fun c =>
      c.depth == 2 && c.mergedInto.any (·.getPrefix == baNs)) do
    throwError "claim 3: expected a depth-2 compl ∘ compl product \
certified back into canonical vocabulary"
  -- ── claim 4: the witness kit certifies refutations ──
  let refutations := r.corpus.facts.filter fun f =>
    f.name.toString.endsWith "_refuted"
  unless refutations.size ≥ 1 do
    throwError "claim 4: the Bool/Bool² kit should certify at least one \
refutation"
  -- ── claim 5: the economy carries over; audit clean ──
  let cc := r.ledger.counts `order_complementer
  unless cc.conceptsAliased ≥ 2 do
    throwError "claim 5: the complementer should earn certified aliases"
  unless (← auditInvented r.pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  IO.println ""
  IO.println s!"corpus: {r.corpus.facts.size} kernel-certified facts \
({refutations.size} refutations); complementer aliased \
{cc.conceptsAliased}"
  IO.println "the stack generalizes: claims 1–5 hold on BooleanAlgebra \
— the first instance-shaped carrier"
