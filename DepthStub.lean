import Eureka

/-!
Deterministic depth-economy tests (DESIGN_DEPTH acceptance tests 2–4).
Test 1 (escalation over a real open class) is the matroid run
(`MatroidDepthRun.lean`); test 5 is the existing suite, which passes
unchanged because cheap/standard admissions still price at 1.0.

- **Tiers classify and price** (test 4): the rung classifier maps
  grounded/refl → cheap, omega/simp → standard, composed/tauto/aesop →
  deep; at equal admission volume a deep prover out-earns a standard
  one.
- **The induction rung works** (test 2): `∀ n, double2 n = 2 * n` for a
  recursive `double2` is open on the cheap ladder — refutation is
  silent (it is true), simp's equations cannot fire on an opaque
  argument, omega sees an atom — and proved under `escalate` by
  induction, admitted through the gate, classified `escalated`.
- **Vindication pays** (test 3): an inventor births a novel concept and
  is killed for garbage; another agent's clone later merges *into* the
  dead inventor's concept — the prober earns the alias, the dead
  inventor earns `conceptAttracted`.
- **Escalation inside the population** (P1/P5): statements the cheap
  ladder leaves open are re-judged by the per-generation escalation
  pass and land as escalated-tier admissions paying the original
  proposer.

Run with `lake env lean DepthStub.lean`.
-/

open Lean Meta Eureka.Runtime

def natTy : Expr := mkConst ``Nat
def natToProp : Expr := Expr.forallE `n natTy (.sort .zero) .default

#eval show MetaM Unit from do
  IO.println "━━ test 4: tiers classify and price ━━"
  for (rung, tier) in [("grounded: Nat.one_add", Tier.cheap),
      ("refl (folded)", .cheap), ("known, symm", .cheap),
      ("omega", .standard), ("simp[corpus]", .standard),
      ("composed: Nat.le_trans + Nat.lt_irrefl", .deep),
      ("by tauto (expanded)", .deep), ("aesop", .deep),
      ("escalated: induction", .escalated)] do
    unless tierOfRung rung == tier do
      throwError "tierOfRung {rung} misclassified"
  let mut l : Ledger := {}
  for _ in [0:5] do
    l := l.record `plainT (.factAdmitted .standard)
    l := l.record `deepT (.factAdmitted .deep)
  let w := fun (a : Name) => l.worth {} (fun _ => #[]) a
  unless w `deepT > w `plainT do
    throwError "equal volume: deep must out-earn standard, got \
{w `deepT} ≤ {w `plainT}"
  IO.println "  ✓ classifier correct; depth out-earns ease at equal volume"

/-- Recursive, simp-taggable, and opaque to the cheap ladder on a free
argument. -/
@[simp] def double2 : Nat → Nat
  | 0 => 0
  | n + 1 => double2 n + 2

#eval show MetaM Unit from do
  IO.println ""
  IO.println "━━ test 2: the induction rung ━━"
  let known ← collectKnown [`Nat]
  let stmt ← withLocalDeclD `n natTy fun n => do
    mkForallFVars #[n] (← mkEq (← mkAppM ``double2 #[n])
                               (← mkAppM ``HMul.hMul #[mkNatLit 2, n]))
  let conj : Conjecture := { name := `double2_eq, stmt, origin := `test }
  let (_, o1) ← judge known {} conj
  let .stillOpen := o1
    | throwError "the cheap ladder should leave double2_eq open"
  let deep : ProbeCtx := { known }
  let (c2, o2) ← escalate deep {} conj
  let .admitted _ note := o2
    | throwError "escalation should prove double2_eq"
  unless note == "escalated: induction" do
    throwError "expected the induction rung, got {note}"
  unless tierOfRung note == .escalated do
    throwError "escalated note misclassified"
  unless c2.facts.size == 1 do
    throwError "the escalated proof should be gate-admitted"
  IO.println s!"  ✓ open on the cheap ladder; proved by induction; \
kernel-gated ({note})"

/-! Test 3: vindication — the grand-run scenario in miniature. -/

def inventorH : Agent where
  name := `inventor
  propose := fun _ => do
    if (← getEnv).contains (inventedNs ++ `quadish) then return #[]
    let v ← withLocalDeclD `n natTy fun n => do
      mkLambdaFVars #[n]
        (← mkEq (← mkAppM ``HMod.hMod #[n, mkNatLit 4]) (mkNatLit 0))
    let idV ← withLocalDeclD `n natTy fun n => mkLambdaFVars #[n] n
    let mut out : Array RProposal :=
      #[.concept { name := `quadish, type := natToProp, value := v }]
    for i in [1:13] do
      out := out.push (.concept
        { name := .mkSimple s!"garbage_{i}",
          type := Expr.forallE `n natTy natTy .default, value := idV })
    return out

def aliaserH : Agent where
  name := `aliaser
  propose := fun _ => do
    unless (← getEnv).contains (inventedNs ++ `quadish) do return #[]
    if (← getEnv).contains (inventedNs ++ `quadish2) then return #[]
    let v ← withLocalDeclD `n natTy fun n => do
      mkLambdaFVars #[n]
        (← mkEq (← mkAppM ``HMod.hMod #[n, mkNatLit 4]) (mkNatLit 0))
    return #[.concept { name := `quadish2, type := natToProp, value := v }]

#eval show MetaM Unit from do
  IO.println ""
  IO.println "━━ test 3: vindication pays the dead ━━"
  let known ← collectKnown [`Nat]
  let r ← evolveWith [inventorH, aliaserH]
    { generations := 2, judgeBudget := 5, probeCtx := some { known } }
  unless r.dead.contains `inventor do
    throwError "the inventor should be killed for its garbage"
  unless (r.ledger.counts `aliaser).conceptsAliased == 1 do
    throwError "the aliaser's clone should merge into quadish"
  unless (r.ledger.counts `inventor).attracted == 1 do
    throwError "the dead inventor should be paid attracted credit, got \
{(r.ledger.counts `inventor).attracted}"
  IO.println "  ✓ inventor killed; its concept attracted a bridge; \
posthumous credit landed"

/-! Escalation inside the population (P1/P5). -/

def stubbornH (ctr : IO.Ref Nat) : Agent where
  name := `stubborn
  propose := fun _ => do
    let k ← ctr.get
    ctr.set (k + 3)
    let mut out : Array RProposal := #[]
    for i in [1:4] do
      let j := k + i
      let stmt ← withLocalDeclD `n natTy fun n => do
        let lhs ← mkAppM ``double2 #[← mkAppM ``HAdd.hAdd #[n, mkNatLit j]]
        let rhs ← mkAppM ``HAdd.hAdd
          #[← mkAppM ``HMul.hMul #[mkNatLit 2, n], mkNatLit (2 * j)]
        mkForallFVars #[n] (← mkEq lhs rhs)
      out := out.push (.fact
        { name := .mkSimple s!"stub_{j}", stmt, origin := `stubborn })
    return out

#eval show MetaM Unit from do
  IO.println ""
  IO.println "━━ escalation inside the population ━━"
  let known ← collectKnown [`Nat]
  let ctr ← IO.mkRef 0
  let r ← evolveWith [stubbornH ctr]
    { generations := 2, judgeBudget := 10,
      escalationBudget := 2, deepCtx := some { known } }
  let cs := r.ledger.counts `stubborn
  unless cs.opens ≥ 3 do
    throwError "the cheap ladder should leave the double2 family open"
  unless cs.admittedDeep ≥ 1 do
    throwError "escalation should close at least one, at the escalated \
tier — got {cs.admittedDeep}"
  IO.println s!"  ✓ {cs.admittedDeep} escalated admissions from \
{cs.opens} opens; proposer paid at tier"
  IO.println ""
  IO.println "depth economy behaves as specified"
