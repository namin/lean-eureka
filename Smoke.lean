import Eureka

/-!
Smoke test: a heuristic proposes one honest fact, one false fact with a
type-incorrect proof, and one `sorry`-backed fact. The gate must admit
exactly the first. Run with `lake env lean Smoke.lean`.
-/

open Lean Meta Eureka.Runtime

def demoHeuristic : Heuristic where
  name := `demo
  propose _ := do
    let two := mkNatLit 2
    let four := mkNatLit 4
    let five := mkNatLit 5
    let sum ← mkAppM ``Nat.add #[two, two]
    let good : FactProposal :=
      { name := `demo.good, stmt := ← mkEq sum four, proof := ← mkEqRefl four }
    let bad : FactProposal :=
      { name := `demo.bad, stmt := ← mkEq sum five, proof := ← mkEqRefl four }
    let lazy : FactProposal :=
      { name := `demo.lazy, stmt := ← mkEq sum five,
        proof := ← mkSorry (← mkEq sum five) false }
    return #[good, bad, lazy]

/-- The adversary: a heuristic with full `MetaM` power that mints an axiom
asserting a falsehood and proposes a "fact" proved from it. The proof
type-checks — the screen cannot catch it; the axiom audit must. -/
def evilHeuristic : Heuristic where
  name := `evil
  propose _ := do
    let sum ← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 2]
    let stmt ← mkEq sum (mkNatLit 5)
    addDecl <| .axiomDecl
      { name := `demo.evilAx, levelParams := [], type := stmt, isUnsafe := false }
    return #[{ name := `demo.evil, stmt, proof := mkConst `demo.evilAx }]

#eval show MetaM Unit from do
  let (corpus, admitted, rejected) ← fire demoHeuristic {}
  IO.println s!"admitted: {admitted.toList.map (·.name)}"
  IO.println s!"rejected: {rejected.toList.map (·.name)}"
  unless admitted.toList.map (·.name) == [`demo.good] do
    throwError "gate admitted the wrong set"
  unless rejected.toList.map (·.name) == [`demo.bad, `demo.lazy] do
    throwError "gate rejected the wrong set"
  -- The adversarial round: the minted axiom passes the screen (the proof
  -- really does type-check) and the kernel accepts it; only the axiom audit
  -- stands between it and the corpus.
  let (corpus, evilAdmitted, evilRejected) ← fire evilHeuristic corpus
  IO.println s!"evil admitted: {evilAdmitted.toList.map (·.name)}"
  IO.println s!"evil rejected: {evilRejected.toList.map (·.name)}"
  unless evilAdmitted.isEmpty do
    throwError "gate admitted an axiom-backed falsehood"
  unless evilRejected.toList.map (·.name) == [`demo.evil] do
    throwError "gate rejected the wrong set in the evil round"
  -- Boundary of the guarantee: the heuristic littered the ambient
  -- environment (its axiom persists), but the rolled-back theorem is gone
  -- and the corpus never depends on the litter — every admission is audited.
  unless (← getEnv).contains `demo.evilAx do
    throwError "expected the minted axiom to persist in the ambient env"
  if (← getEnv).contains `demo.evil then
    throwError "rollback failed: refused theorem persists"
  -- Laundering attempt: an honest-looking proposal referencing the litter is
  -- still refused at admission.
  let laundered : FactProposal :=
    { name := `demo.laundered
      stmt := ← mkEq (← mkAppM ``Nat.add #[mkNatLit 2, mkNatLit 2]) (mkNatLit 5)
      proof := mkConst `demo.evilAx }
  unless (← commitFact laundered).isNone do
    throwError "gate laundered a polluted proof into the corpus"
  unless corpus.facts.toList.map (·.name) == [`demo.good] do
    throwError "corpus does not contain exactly the honest fact"
  IO.println "gate behaves as specified"
