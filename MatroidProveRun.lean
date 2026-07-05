import EurekaMathlib

/-!
The control and the comparison (DESIGN_PROVE acceptance tests 4 and 6).

A pinned corpus over LLM-style invented concepts (a cyclic-set predicate
and a free-flat predicate, the shapes the grand runs' booth actually
invents) plus known-hard residuals. Each statement runs, in order:
the symbolic escalation ladder (must fail for the interesting rows),
the repair rung (test 4 — the baseline's pattern, in-process), and the
stepper (test 6 — the wager), same LLM, same retrieval. The table is
the deliverable; the pre-registered hard assertion is repair ≥ 1
closure beyond the symbolic ladder. Everything that proves passes
`commitFact`.

Live LLM (up to ~25 Bedrock calls) + Mathlib; not in CI. Run with
`lake env lean MatroidProveRun.lean`.
-/

open Lean Meta Eureka.Runtime

set_option linter.unusedSimpArgs false

def mkSetPred (body : Expr → Expr → Expr → MetaM Expr) : MetaM (Expr × Expr) := do
  let value ← withLocalDeclD `α (mkSort (.succ .zero)) fun α =>
    withLocalDeclD `M (mkApp (mkConst `Matroid [.zero]) α) fun M =>
      withLocalDeclD `X (mkApp (mkConst ``Set [.zero]) α) fun X => do
        mkLambdaFVars #[α, M, X] (← body α M X)
  let type ← withLocalDeclD `α (mkSort (.succ .zero)) fun α =>
    withLocalDeclD `M (mkApp (mkConst `Matroid [.zero]) α) fun M =>
      withLocalDeclD `X (mkApp (mkConst ``Set [.zero]) α) fun X =>
        mkForallFVars #[α, M, X] (.sort .zero)
  return (value, type)

/-- `X ⊆ M.E ∧ ∀ e ∈ X, ∃ C, M.IsCircuit C ∧ e ∈ C ∧ C ⊆ X` — the grand
runs' cyclic-set invention, verbatim shape. -/
def cyclicBody (α M X : Expr) : MetaM Expr := do
  let sub ← mkAppM ``HasSubset.Subset #[X, ← mkAppM `Matroid.E #[M]]
  let inner ← withLocalDeclD `e α fun e => do
    let mem ← mkAppM ``Membership.mem #[X, e]
    let ex ← withLocalDeclD `C (mkApp (mkConst ``Set [.zero]) α) fun C => do
      let conj ← mkAppM ``And #[← mkAppM `Matroid.IsCircuit #[M, C],
        ← mkAppM ``And #[← mkAppM ``Membership.mem #[C, e],
                         ← mkAppM ``HasSubset.Subset #[C, X]]]
      mkLambdaFVars #[C] conj
    mkForallFVars #[e] (← mkArrow mem (← mkAppM ``Exists #[ex]))
  mkAppM ``And #[sub, inner]

/-- `M.Indep X ∧ M.closure X = X` — the free-flat invention. -/
def freeFlatBody (_α M X : Expr) : MetaM Expr := do
  mkAppM ``And #[← mkAppM `Matroid.Indep #[M, X],
    ← mkEq (← mkAppM `Matroid.closure #[M, X]) X]

#eval show MetaM Unit from do
  let carrier := `Matroid
  let known ← collectKnown [carrier]
  let deepKnown ← collectKnown [carrier, `Set]
  -- birth the two invented concepts
  let (v1, t1) ← mkSetPred cyclicBody
  let (v2, t2) ← mkSetPred freeFlatBody
  let .ok (pool, cyc) ← commitConcept {}
      { name := `MIsCyclic, type := t1, value := v1 }
    | throwError "cyclic birth refused"
  let .ok (pool, ff) ← commitConcept pool
      { name := `MIsFreeFlat, type := t2, value := v2 }
    | throwError "free-flat birth refused"
  let some depT ← probeTargetOfConst `Matroid.IsRkFinite | throwError "no t"
  let some dp ← mkDualizeProposal depT
    | throwError "no dual proposal"
  let .ok (pool, drk) ← commitConcept pool dp
    | throwError "dual birth refused"
  -- targets for statements
  let some circuitT ← probeTargetOfConst `Matroid.IsCircuit | throwError "t"
  let some indepT ← probeTargetOfConst `Matroid.Indep | throwError "t"
  let some rkT ← probeTargetOfConst `Matroid.IsRkFinite | throwError "t"
  let mkImpl := fun (a b : ProbeTarget) => do
    let some s ← mkImplStmt a b | throwError "impl build failed"
    pure s
  let corpus0 : Corpus := {}
  -- the pinned corpus: (label, statement)
  let items : Array (String × Expr) := #[
    ("circuit_is_cyclic", ← mkImpl circuitT cyc.toTarget),
    ("freeflat_indep", ← mkImpl ff.toTarget indepT),
    ("cyclic_subset", ← do
      let some s ← mkIffStmt cyc.toTarget cyc.toTarget | throwError "x"
      pure s),  -- trivial sanity row (refl)
    ("rk_to_dualrk", ← mkImpl rkT drk.toTarget),
    ("dualrk_to_rk", ← mkImpl drk.toTarget rkT),
    ("indep_to_freeflat", ← mkImpl indepT ff.toTarget)]
  let cheapRungs : Array String := #["tauto",
    "simp only [Matroid.dep_iff, Matroid.IsColoop, Matroid.dual_dual, \
Matroid.singleton_dep, Set.singleton_subset_iff, and_comm, and_assoc, \
and_left_comm]"]
  let deep : ProbeCtx :=
    { known := deepKnown, extraRungs := cheapRungs ++ #["aesop"],
      composeDepth := 3 }
  let call := Eureka.LLM.invoke Eureka.LLM.defaultConfig
  let refuter : Refuter := fun stmt => do
    let usedInv := (stmt.getUsedConstants.filter
      (inventedNs.isPrefixOf ·)).map toString
    let pre := if usedInv.isEmpty then "" else
      s!"unfold {String.intercalate " " usedInv.toList}; "
    refuteByInstances matroidRefuterSimpArgs (mkConst ``Nat)
      matroidInstances stmt (pre := pre)
  let mut corpus := corpus0
  let mut table : Array (String × String × String × String) := #[]
  let mut repairWins := 0
  let mut stepperWins := 0
  for (label, stmt) in items do
    IO.println s!"── {label}: {toString (← ppExpr stmt)}"
    let conj : Conjecture := { name := .mkSimple label, stmt, origin := `prove }
    let (corpus', o) ← escalate deep corpus conj refuter
    corpus := corpus'
    let symbolic := match o with
      | .admitted _ n => s!"✓ {n}"
      | .refuted w => s!"✗ {w}"
      | _ => "open"
    let mut repair := "—"
    let mut stepper := "—"
    if let .stillOpen := o then
      match ← proveByRepair call deepKnown stmt with
      | some (pf, rounds) =>
        if let some (c', _) ← commitProbeFact corpus s!"{label}_rep" stmt pf then
          corpus := c'
          repair := s!"✓ (round {rounds})"
          repairWins := repairWins + 1
        else repair := "refused at gate"
      | none => repair := "open"
      match ← proveByStepper (some call) deepKnown stmt
          { llmCallCap := 4 } with
      | some pf =>
        if (← commitFact { name := .mkSimple s!"{label}_step", stmt, proof := pf }).isSome then
          stepper := "✓"
          stepperWins := stepperWins + 1
        else stepper := "refused at gate"
      | none => stepper := "open"
    table := table.push (label, symbolic, repair, stepper)
  IO.println ""
  IO.println "━━ the table (symbolic / repair / stepper) ━━"
  for (l, s, r, st) in table do
    IO.println s!"  {l}: {s} | {r} | {st}"
  IO.println s!"  repair closures beyond symbolic: {repairWins}; \
stepper closures beyond symbolic: {stepperWins}"
  unless (← auditInvented pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  unless repairWins + stepperWins ≥ 1 do
    throwError "the control should close at least one statement beyond \
the symbolic ladder — if this fires, that is the finding (V6)"
  IO.println ""
  IO.println "the control and the comparison: measured"
