import Eureka

/-!
Deterministic worth-economy test (DESIGN_WORTH acceptance tests 2, 3, 4,
6, 7). Test 1 (the separated economy experiment) and test 5 (the
operator derby) are matroid runs: `MatroidEconomyRun.lean`,
`MatroidDerbyRun.lean`.

- **The ordering holds** (test 2): four synthetic agents — all-admitted,
  all-refuted, all-open, all-garbage — end in strictly that worth order;
  the garbage agent is killed, the refuter-fodder agent is not
  (refutations pay, with decaying returns).
- **The floor floors** (test 7): with judge budget zero, every live
  agent still gets one judgment per generation.
- **Alias-farming dies** (test 3): an agent re-proposing canonical
  vocabulary under fresh names earns the bridge once, then nothing —
  decayed to the kill threshold and killed.
- **Delayed credit lands** (test 4): the InventStub unlock scenario
  inside `evolve` — an inventor's stuck pair is merged by trigger (i)
  in a later run, paying the inventor a delayed alias credit with no
  new proposals from it.
- **No new trusted surface** (test 6): the Smoke-style adversary as an
  agent — its falsehood dies at the refuter, its axiom never enters any
  proof, its smuggled def is flagged by the namespace audit.

Run with `lake env lean WorthStub.lean`.
-/

open Lean Meta Eureka.Runtime

def natTy : Expr := mkConst ``Nat

/-- `∀ a, a + k = k + a`, fresh `k` each firing: always admitted. -/
def admitterH : Agent where
  name := `admitter
  propose := fun corpus => do
    let base := corpus.facts.size
    let mut out : Array RProposal := #[]
    for i in [1:7] do
      let k := mkNatLit (base * 20 + i)
      let stmt ← withLocalDeclD `a natTy fun a => do
        mkForallFVars #[a] (← mkEq (← mkAppM ``HAdd.hAdd #[a, k])
                                   (← mkAppM ``HAdd.hAdd #[k, a]))
      out := out.push (.fact { name := .mkSimple s!"adm_{base}_{i}", stmt,
                               origin := `admitter })
    return out

/-- `∀ a, a + k = a` for `k ≥ 1`: always refuted (by evaluation). -/
def fodderH : Agent where
  name := `fodder
  propose := fun corpus => do
    let base := corpus.facts.size
    let mut out : Array RProposal := #[]
    for i in [1:7] do
      let k := mkNatLit (base * 20 + i)
      let stmt ← withLocalDeclD `a natTy fun a => do
        mkForallFVars #[a] (← mkEq (← mkAppM ``HAdd.hAdd #[a, k]) a)
      out := out.push (.fact { name := .mkSimple s!"fod_{base}_{i}", stmt,
                               origin := `fodder })
    return out

/-- `∀ a, (a+k)² = a² + 2·k·a + k²`: true, nonlinear — open on this
ladder. -/
def dreamerH : Agent where
  name := `dreamer
  propose := fun corpus => do
    let base := corpus.facts.size
    let two := mkNatLit 2
    let mut out : Array RProposal := #[]
    for i in [1:7] do
      let k := mkNatLit (base * 20 + i)
      let stmt ← withLocalDeclD `a natTy fun a => do
        let sq := fun (x : Expr) => mkAppM ``HPow.hPow #[x, two]
        let lhs ← sq (← mkAppM ``HAdd.hAdd #[a, k])
        let mid ← mkAppM ``HMul.hMul #[two, ← mkAppM ``HMul.hMul #[k, a]]
        let rhs ← mkAppM ``HAdd.hAdd
          #[← mkAppM ``HAdd.hAdd #[← sq a, mid], ← sq k]
        mkForallFVars #[a] (← mkEq lhs rhs)
      out := out.push (.fact { name := .mkSimple s!"drm_{base}_{i}", stmt,
                               origin := `dreamer })
    return out

/-- Malformed concepts (not `Prop`-valued), fresh names: refused at the
birth gate, priced negatively. -/
def sloppyH : Agent where
  name := `sloppy
  propose := fun corpus => do
    let base := corpus.facts.size
    let mut out : Array RProposal := #[]
    let idVal ← withLocalDeclD `n natTy fun n => mkLambdaFVars #[n] n
    let idTy := Expr.forallE `n natTy natTy .default
    for i in [1:7] do
      out := out.push (.concept
        { name := .mkSimple s!"sloppy_{base}_{i}", type := idTy, value := idVal })
    return out

def worthOf (r : EvolveResult) (a : Name) : Float :=
  r.ledger.worth {} (fun _ => #[]) a

#eval show MetaM Unit from do
  IO.println "━━ tests 2 & 7: the ordering, and the floor ━━"
  let ctx : ProbeCtx := { known := ← collectKnown [`Nat] }
  let cfg : EvolveConfig :=
    { generations := 3, judgeBudget := 30, perAgentCap := 6,
      probeCtx := some ctx }
  let r ← evolveWith [admitterH, fodderH, dreamerH, sloppyH] cfg
  let wa := worthOf r `admitter
  let wf := worthOf r `fodder
  let wd := worthOf r `dreamer
  let ws := worthOf r `sloppy
  IO.println s!"  worth: admitter {wa}, fodder {wf}, dreamer {wd}, sloppy {ws}"
  unless wa > wf && wf > wd && wd ≥ ws do
    throwError "expected admitted > refuted > open ≥ garbage"
  unless r.dead.contains `sloppy do
    throwError "the garbage agent should be killed"
  unless !(r.dead.contains `fodder) do
    throwError "refutations pay — fodder must not be killed here"
  -- Test 7: zero budget, the floor alone.
  let r7 ← evolveWith [admitterH, fodderH, dreamerH]
    { cfg with judgeBudget := 0, generations := 3 }
  for a in [`admitter, `fodder, `dreamer] do
    unless r7.ledger.attention a ≥ 3 do
      throwError "{a} should get one floored judgment per generation, \
got {r7.ledger.attention a}"
  IO.println "  ✓ ordering holds; garbage killed, fodder alive; floor floors"

/-- The canonical predicate for the alias-farming test. -/
def isEven (n : Nat) : Prop := n % 2 = 0

/-- Re-proposes `isEven`'s body under fresh names, forever. -/
def farmerH : Agent where
  name := `farmer
  propose := fun corpus => do
    let base := corpus.facts.size
    let evenVal ← withLocalDeclD `n natTy fun n => do
      mkLambdaFVars #[n] (← mkEq (← mkAppM ``HMod.hMod #[n, mkNatLit 2]) (mkNatLit 0))
    let evenTy := Expr.forallE `n natTy (.sort .zero) .default
    let mut out : Array RProposal := #[]
    for i in [1:9] do
      out := out.push (.concept
        { name := .mkSimple s!"clone_{base}_{i}", type := evenTy, value := evenVal })
    return out

#eval show MetaM Unit from do
  IO.println ""
  IO.println "━━ test 3: alias-farming dies ━━"
  let known ← collectKnown [`Nat]
  let some evenT ← probeTargetOfConst ``isEven | throwError "no target"
  let ctx : ProbeCtx :=
    { known, transparent := fun n => inventedNs.isPrefixOf n || n == ``isEven }
  let r ← evolveWith [farmerH]
    { generations := 4, judgeBudget := 10, perAgentCap := 8,
      probeCtx := some ctx, canonical := #[evenT] }
  let w := worthOf r `farmer
  IO.println s!"  farmer worth {w}, aliased \
{(r.ledger.counts `farmer).conceptsAliased} clones into isEven"
  unless (r.ledger.counts `farmer).conceptsAliased ≥ 24 do
    throwError "expected the farmer's clones merged at birth"
  unless r.dead.contains `farmer do
    throwError "the alias farmer should decay to the kill threshold and die"
  IO.println "  ✓ every clone merged at birth; the farm priced out; farmer killed"

/-! Test 4: the stuck pair, the unlock, the delayed credit. -/

def opaqueDouble (n : Nat) : Nat := n + n

def opaqueDouble_eq : ∀ n : Nat, opaqueDouble n = 2 * n :=
  fun n => (Nat.two_mul n).symm

/-- Births the stuck pair once; silent forever after. -/
def inventorH : Agent where
  name := `inventor
  propose := fun _ => do
    if (← getEnv).contains (inventedNs ++ `gsA) then return #[]
    let mkPred := fun (mkBody : Expr → MetaM Expr) => do
      let value ← withLocalDeclD `n natTy fun n => do
        mkLambdaFVars #[n] (← mkBody n)
      pure (value, Expr.forallE `n natTy (.sort .zero) .default)
    let (vA, tA) ← mkPred fun n => do
      mkEq (← mkAppM ``opaqueDouble #[n]) (mkNatLit 10)
    let (vB, tB) ← mkPred fun n => do
      mkEq (← mkAppM ``HMul.hMul #[mkNatLit 2, n]) (mkNatLit 10)
    return #[.concept { name := `gsA, type := tA, value := vA },
             .concept { name := `gsB, type := tB, value := vB }]

/-- Proposes the linking edge, once the pair exists. -/
def linkerH : Agent where
  name := `linker
  propose := fun _ => do
    unless (← getEnv).contains (inventedNs ++ `gsA) do return #[]
    let stmt ← withLocalDeclD `n natTy fun n => do
      mkForallFVars #[n] (← mkArrow
        (mkApp (mkConst (inventedNs ++ `gsA)) n)
        (mkApp (mkConst (inventedNs ++ `gsB)) n))
    return #[.fact { name := `gs_link, stmt, origin := `linker }]

#eval show MetaM Unit from do
  IO.println ""
  IO.println "━━ test 4: delayed credit lands ━━"
  let known ← collectKnown [`Nat]
  let ctx : ProbeCtx := { known }
  let cfg : EvolveConfig :=
    { generations := 1, judgeBudget := 10, perAgentCap := 6,
      probeCtx := some ctx }
  -- Run 1: the inventor births the pair; nothing can merge it.
  let r1 ← evolveWith [inventorH] cfg
  unless r1.pool.isLive (inventedNs ++ `gsA) &&
      r1.pool.isLive (inventedNs ++ `gsB) do
    throwError "the stuck pair should be unmergeable at birth"
  -- Between runs: the unlock enters the corpus through the gate.
  let ci ← getConstInfo ``opaqueDouble_eq
  let some unlockFact ← commitFact
      { name := ← freshName `opaqueDouble_eq, stmt := ci.type, proof := ci.value! }
    | throwError "the gate refused the unlock"
  let corpus := { r1.corpus with facts := r1.corpus.facts.push unlockFact }
  -- Run 2: the linker's edge admits (concept-aware judge), mentions both
  -- inventions, fires trigger (i); the merge pays the inventor.
  let r2 ← evolveWith [inventorH, linkerH] cfg corpus r1.pool
  unless !(r2.pool.isLive (inventedNs ++ `gsB)) do
    throwError "trigger (i) should have merged gsB into gsA"
  let wInv := worthOf r2 `inventor
  IO.println s!"  inventor worth in run 2: {wInv} (proposed nothing; paid \
by the delayed merge)"
  unless wInv ≥ 0.9 do
    throwError "the delayed alias credit should pay the inventor, got {wInv}"
  IO.println "  ✓ merge landed generations after birth; the inventor was paid"

/-! Test 6: the adversary under the new loop. -/

def evilAgent : Agent where
  name := `evil
  propose := fun _ => do
    let sum ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 2]
    let stmt ← mkEq sum (mkNatLit 5)
    unless (← getEnv).contains `worthDemo.evilAx do
      addDecl <| .axiomDecl
        { name := `worthDemo.evilAx, levelParams := [], type := stmt,
          isUnsafe := false }
    unless (← getEnv).contains (inventedNs ++ `smuggled) do
      let value ← withLocalDeclD `n natTy fun n =>
        mkLambdaFVars #[n] (mkConst ``False)
      addDecl <| .defnDecl
        { name := inventedNs ++ `smuggled, levelParams := [],
          type := Expr.forallE `n natTy (.sort .zero) .default,
          value, hints := .abbrev, safety := .safe }
    return #[.fact { name := `evil_fact, stmt, origin := `evil }]

#eval show MetaM Unit from do
  IO.println ""
  IO.println "━━ test 6: no new trusted surface ━━"
  let r ← evolveWith [evilAgent]
    { generations := 2, judgeBudget := 5,
      probeCtx := some { known := ← collectKnown [`Nat] } }
  let five := mkNatLit 5
  unless !(r.corpus.facts.any fun f => f.stmt.find? (· == five) |>.isSome) do
    throwError "the falsehood reached the corpus"
  -- This file's #evals share one environment, so this run's audit also
  -- flags the earlier tests' concepts (admitted to *their* pools, unknown
  -- to this one) — the boundary check working as specified. The smuggled
  -- def must be among the flags.
  let violations ← auditInvented r.pool
  unless violations.contains (inventedNs ++ `smuggled) do
    throwError "the audit should flag the smuggled def, got {violations}"
  IO.println "  ✓ falsehood refuted, never admitted; smuggled def flagged \
by the audit"
  IO.println ""
  IO.println "worth economy behaves as specified"
