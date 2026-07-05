import Eureka
import Mathlib

/-!
# Mathlib domains: predicates from a namespace, no seed files

The low-guidance move: the user names a Mathlib namespace (e.g. `Matroid`);
the system extracts its predicates from the environment by signature shape,
generates relational conjectures between them, and probes invented
predicates for kernel-certified aliases. No hand-written seed JSON, no
curated canonical pool — the environment is both.

This is the in-process answer to the formal-disco alignment toolchain: the
probes that took ~75s each as `lake env lean` subprocesses (BRAINSTORM_ALIGN
facet 1.B) are `MetaM` calls against an environment that is already loaded.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- The argument shape of a collected predicate. -/
inductive PredShape where
  | element  -- `Matroid α → α → Prop`
  | set      -- `Matroid α → Set α → Prop`
  deriving BEq

structure PredInfo where
  name : Name
  shape : PredShape

/-- Collect predicates `Carrier α → α → Prop` and `Carrier α → Set α → Prop`
from a namespace, where `Carrier` is the namespace's structure itself
(e.g. `Matroid`). -/
def collectPredicates (carrier : Name) : MetaM (Array PredInfo) := do
  let env ← getEnv
  let cands : Array (Name × Expr) :=
    env.constants.fold (init := #[]) fun acc n ci =>
      if n.getPrefix == carrier && !n.isInternal then
        match ci with
        | .defnInfo t =>
          match t.levelParams with
          | [u] => acc.push (n, t.type.instantiateLevelParams [u] [Level.zero])
          | _ => acc
        | _ => acc
      else acc
  let mut out := #[]
  for (n, ty) in cands do
    let shape? ← attempt <| forallTelescope ty fun xs body => do
      unless body == .sort .zero do return none
      unless xs.size == 3 do return none
      let αTy ← inferType xs[0]!
      unless αTy.isSort do return none
      let mTy ← inferType xs[1]!
      unless mTy.getAppFn.constName? == some carrier do return none
      let xTy ← inferType xs[2]!
      if xTy == xs[0]! then
        return some PredShape.element
      if xTy.getAppFn.constName? == some ``Set && xTy.getAppArgs == #[xs[0]!] then
        return some PredShape.set
      return none
    if let some (some shape) := shape? then
      out := out.push { name := n, shape }
  return out.qsort (fun a b => a.name.toString < b.name.toString)

/-- Build `∀ (α : Type) (M : Carrier α) (x : _), <mk body>` for a shape. -/
def mkPredForall (carrier : Name) (shape : PredShape)
    (mkBody : Expr → Expr → MetaM Expr) : MetaM Expr := do
  withLocalDeclD `α (mkSort (.succ .zero)) fun α => do
    let carrierTy := mkApp (mkConst carrier [Level.zero]) α
    withLocalDeclD `M carrierTy fun M => do
      let xTy := match shape with
        | .element => α
        | .set => mkApp (mkConst ``Set [Level.zero]) α
      withLocalDeclD `X xTy fun X => do
        mkForallFVars #[α, M, X] (← mkBody M X)

/-- Conjecture `∀ α M X, P M X → Q M X` for same-shape predicates. -/
def mkImplConjecture (carrier : Name) (P Q : PredInfo) : MetaM Conjecture := do
  let stmt ← mkPredForall carrier P.shape fun M X => do
    mkArrow (← mkAppM P.name #[M, X]) (← mkAppM Q.name #[M, X])
  return { name := .mkSimple s!"{P.name.getString!}_imp_{Q.name.getString!}",
           stmt, origin := `implication }

/-- Conjecture `∀ α M X, F M X ↔ P M X` — the alias probe for an invented
predicate `F` against a canonical one `P`. -/
def mkIffConjecture (carrier : Name) (shape : PredShape) (F P : Name) :
    MetaM Conjecture := do
  let stmt ← mkPredForall carrier shape fun M X => do
    return mkApp2 (mkConst ``Iff) (← mkAppM F #[M, X]) (← mkAppM P #[M, X])
  return { name := .mkSimple s!"{F.getString!}_alias_{P.getString!}",
           stmt, origin := `alias }

/-- Map the implication structure among a namespace's predicates: judge
`P → Q` for every ordered pair of same-shape predicates. Admitted edges are
kernel-certified; there is no counterexample search in this domain, so
non-theorems land in `open` and are reported as such. -/
def implicationSweep (known : Array KnownLemma) (carrier : Name)
    (preds : Array PredInfo) (corpus : Corpus) :
    MetaM (Corpus × Nat × Array String) := do
  let mut corpus := corpus
  let mut opens : Array String := #[]
  let mut admitted := 0
  for P in preds do
    for Q in preds do
      if P.name != Q.name && P.shape == Q.shape then
        -- One candidate, one heartbeat budget: budgets are cumulative per
        -- command, and a sweep must not starve its own tail.
        let (corpus', outcome, pretty) ← withCurrHeartbeats do
          let c ← mkImplConjecture carrier P Q
          let pretty := toString (← ppExpr c.stmt)
          let (corpus', outcome) ← judge known corpus c
          pure (corpus', outcome, pretty)
        corpus := corpus'
        match outcome with
        | .admitted _ note =>
          admitted := admitted + 1
          IO.println s!"  ✓ {pretty} — admitted ({note})"
        | .stillOpen => opens := opens.push pretty
        | .refuted cex => IO.println s!"  ✗ {pretty} — refuted ({cex})"
        | .refusedAtGate => IO.println s!"  ! {pretty} — REFUSED at gate"
  return (corpus, admitted, opens)

/-- A refuter for predicate domains: instantiate a conjecture
`∀ (α : Type) (M : Carrier α) (X : _), body` at concrete instances and try
to prove the *negation* of the instance by simp with a domain-supplied
argument list. Unlike the `Nat` evaluator refuter, a refutation here
carries a kernel-checkable proof of the negated instance — the caller can
pass it through the gate. Instances whose value doesn't fit the
conjecture's shape (set vs element) fail the type check and are skipped;
a refuter this partial is honest by construction: silence leaves the
conjecture open, it never certifies truth. -/
def refuteByInstances (simpArgs : Array String) (carrierVal : Expr)
    (instances : Array (Expr × Expr × String)) (stmt : Expr)
    (pre : String := "") : MetaM (Option (Expr × Expr × String)) := do
  -- `pre` runs before the simp — e.g. `unfold Invented.X; ` for invented
  -- vocabulary, which simp cannot unfold by name (no equation lemmas are
  -- generated for raw `addDecl` definitions; delta works).
  let tac := s!"{pre}simp [{String.intercalate ", " simpArgs.toList}]"
  -- Bounded: open exactly `α M X` and keep the conjecture's implication
  -- arrow inside the body (a plain telescope would take the hypothesis of
  -- `P → Q` as a fourth binder).
  let r ← attempt <| forallBoundedTelescope stmt (some 3) fun xs body => do
    if xs.size != 3 then return none
    for (m, x, desc) in instances do
      let inst := body.replaceFVars xs #[carrierVal, m, x]
      unless (← attempt (check inst)).isSome do continue
      let negStmt := mkApp (mkConst ``Not) inst
      if let some pf ← tryTacticRung tac negStmt then
        return some (negStmt, pf, desc)
    return none
  return r.join

/-- Probe an invented predicate for a certified alias among same-shape
canonical predicates: the generic hunt first (defeq, known-iff lemmas direct
and symmetric, simp, aesop), then a targeted rung that unfolds both
predicates and closes propositionally. Returns the grounding, if any rung
finds one — the certificate is a kernel-checked `iff`. -/
def aliasProbe (known : Array KnownLemma) (carrier : Name) (shape : PredShape)
    (invented : Name) (preds : Array PredInfo) (corpus : Corpus) :
    MetaM (Corpus × Option (Name × String)) := do
  let mut corpus := corpus
  for P in preds do
    if P.shape == shape then
      -- One probe candidate, one heartbeat budget (see implicationSweep).
      let (corpus', found) ← withCurrHeartbeats do
        let c ← mkIffConjecture carrier shape invented P.name
        let (corpus', outcome) ← judge known corpus c
        match outcome with
        | .admitted _ note => return (corpus', some (P.name, note))
        | .stillOpen =>
          for tac in [s!"unfold {invented} {P.name}; tauto",
                      s!"unfold {invented} {P.name}; aesop"] do
            if let some pf ← tryTacticRung tac c.stmt then
              let nm ← freshName c.name
              if let some f ← commitFact { name := nm, stmt := c.stmt, proof := pf } then
                return ({ corpus' with facts := corpus'.facts.push f },
                        some (P.name, s!"by {tac}"))
          -- Transitive: compose a direct step with a known iff bridging to
          -- the canonical side (e.g. is_loop_def ↔ Dep {e} ↔ IsLoop, via
          -- Matroid.singleton_dep).
          let subProve := fun (subStmt : Expr) => do
            let midHead := (← attempt <| forallTelescope subStmt fun _ body =>
              pure ((body.app2? ``Iff).bind (·.2.getAppFn.constName?))).join
            let unfolds := match midHead with
              | some h => s!"{invented} {h}"
              | none => s!"{invented}"
            for tac in [s!"unfold {unfolds}; tauto", s!"unfold {unfolds}; aesop"] do
              if let some pf ← tryTacticRung tac subStmt then
                return some pf
            return (none : Option Expr)
          if let some (pf, bridge) ← tryKnownChain known c.stmt subProve then
            let nm ← freshName c.name
            if let some f ← commitFact { name := nm, stmt := c.stmt, proof := pf } then
              return ({ corpus' with facts := corpus'.facts.push f },
                      some (P.name, s!"chained via {bridge}"))
          return (corpus', none)
        | _ => return (corpus', none)
      corpus := corpus'
      if let some g := found then
        return (corpus, some g)
  return (corpus, none)

end Runtime
end Eureka
