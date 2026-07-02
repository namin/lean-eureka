import Eureka.Runtime

/-!
# The evidence hunt

Heuristics propose conjectures — statements without evidence. The prover
hunts for evidence on the untrusted side of the gate: a counterexample
search that can *refute*, and a ladder of proof rungs that can *support*.
Nothing here is trusted; whatever the hunt returns still has to pass
`commitFact`. Silence (`stillOpen`) is not truth.

The `known` rung doubles as grounding: when a conjecture is definitionally
an existing library lemma, the evidence is that lemma — the discovery is
an alias, and the output says so. This is the in-process answer to the
synonym-tower failure mode.
-/

open Lean Meta Elab

namespace Eureka
namespace Runtime

/-- Outcome of the evidence hunt for one conjecture. -/
inductive Verdict where
  | proved (proof : Expr) (rung : String) (knownAs : Option Name := none)
  | refuted (counterexample : String)
  | stillOpen
  deriving Inhabited

/-- Run one evidence attempt, absorbing *all* failures — including runtime
ones like max-recursion-depth, which plain `try/catch` lets through. This
matters: simp over a corpus of discovered rewrite rules can genuinely
diverge, and a rung that blows up is just a rung that failed. -/
def attempt {α : Type} (x : MetaM α) : MetaM (Option α) :=
  tryCatchRuntimeEx
    (try some <$> x catch _ => return none)
    (fun _ => return none)

/-- `isDefEq` that treats any failure — including runtime blowup — as
"not definitionally equal". -/
def defeqSafe (a b : Expr) : MetaM Bool :=
  return (← attempt (withNewMCtxDepth (isDefEq a b))).getD false

/-- Counterexample search: instantiate up to three `Nat` binders with small
numerals and *evaluate*. Only speaks when an instantiation computes to
`false`; anything short of that is silence, not support. -/
def tryRefute (stmt : Expr) (range : Nat := 4) : MetaM (Option String) := do
  let r ← attempt <| forallTelescope stmt fun xs body => do
      if xs.size > 3 then return none
      for x in xs do
        unless (← inferType x).isConstOf ``Nat do return none
      let n := xs.size
      for idx in [0 : range ^ n] do
        let mut vals : Array Nat := #[]
        let mut k := idx
        for _ in [0 : n] do
          vals := vals.push (k % range)
          k := k / range
        let inst := body.replaceFVars xs (vals.map mkNatLit)
        let d ← try mkDecide inst catch _ => return none
        let r ← whnfD d
        if r.isConstOf ``Bool.false then
          let mut parts : Array String := #[]
          for j in [0 : n] do
            parts := parts.push s!"{← xs[j]!.fvarId!.getUserName} := {vals[j]!}"
          return some (String.intercalate ", " parts.toList)
        unless r.isConstOf ``Bool.true do return none
      return none
  return r.join

/-- Rung 1: the two sides are definitionally equal. -/
def tryRefl (stmt : Expr) : MetaM (Option Expr) := do
  let r ← attempt <| forallTelescope stmt fun xs body => do
      let some (_, lhs, rhs) := body.eq? | return none
      unless ← withNewMCtxDepth (isDefEq lhs rhs) do return none
      return some (← mkLambdaFVars xs (← mkEqRefl lhs))
  return r.join

/-- A library lemma eligible as a grounding certificate, with a cheap
prefilter key (binder count, head constant of the equation's left side). -/
structure KnownLemma where
  name : Name
  type : Expr
  binders : Nat
  lhsHead : Option Name

/-- Collect the grounding pool: universe-monomorphic theorems under the given
namespace prefixes, keyed for the prefilter. -/
def collectKnown (prefixes : List Name) : MetaM (Array KnownLemma) := do
  let env ← getEnv
  let cands : Array (Name × Expr) := env.constants.fold (init := #[]) fun acc n ci =>
    if prefixes.contains n.getPrefix then
      match ci with
      | .thmInfo t => if t.levelParams.isEmpty then acc.push (n, t.type) else acc
      | _ => acc
    else acc
  let mut out := #[]
  for (n, ty) in cands do
    let key ← try
      forallTelescope ty fun xs body =>
        match body.eq? with
        | some (_, lhs, _) => pure (some (xs.size, lhs.getAppFn.constName?))
        | none => pure none
      catch _ => pure none
    if let some (binders, lhsHead) := key then
      out := out.push { name := n, type := ty, binders, lhsHead }
  return out

/-- Rung 2: the conjecture is definitionally an existing library lemma. The
proof is that lemma — and the discovery is thereby *grounded*: it is an
alias, and the caller reports which. -/
def tryKnown (known : Array KnownLemma) (stmt : Expr) :
    MetaM (Option (Expr × Name)) := do
  let key ← forallTelescope stmt fun xs body =>
    match body.eq? with
    | some (_, lhs, _) => pure (some (xs.size, lhs.getAppFn.constName?))
    | none => pure none
  let some (binders, lhsHead) := key | return none
  for k in known do
    if k.binders == binders && k.lhsHead == lhsHead then
      if ← defeqSafe k.type stmt then
        return some (mkConst k.name, k.name)
  return none

/-- Rung 2b: the conjecture is an existing library lemma *stated the other
way around*. The proof is the lemma with `Eq.symm` applied pointwise. -/
def tryKnownSymm (known : Array KnownLemma) (stmt : Expr) :
    MetaM (Option (Expr × Name)) := do
  let r ← attempt <| forallTelescope stmt fun xs body => do
      let some (_, lhs, rhs) := body.eq? | return none
      let symmStmt ← mkForallFVars xs (← mkEq rhs lhs)
      let some (pf, nm) ← tryKnown known symmStmt | return none
      let proof ← mkLambdaFVars xs (← mkEqSymm (mkAppN pf xs))
      return some (proof, nm)
  return r.join

/-- Rungs 3 and 4: simp, with an explicit lemma set. Called first with the
corpus itself — discoveries proving discoveries — and then with the ambient
default simp set. -/
def trySimpWith (lemmas : Array Name) (useDefault : Bool) (stmt : Expr) :
    MetaM (Option Expr) := do
  let r ← attempt do
    let goal ← mkFreshExprMVar stmt
    let mut thms : SimpTheorems := {}
    if useDefault then
      thms ← getSimpTheorems
    for n in lemmas do
      thms ← thms.addConst n
    let ctx ← Simp.mkContext (simpTheorems := #[thms])
      (congrTheorems := ← getSimpCongrTheorems)
    let (result, _) ← simpGoal goal.mvarId! ctx
    match result with
    | none => return some (← instantiateMVars goal)
    | some _ => return none
  return r.join

/-- A generic tactic rung: enter the binders, elaborate `by <tac>` against
the body, and abstract the proof. No `TacticM` plumbing — the elaborator
does the work, and failures (including logged ones) leave no trace. -/
def tryTacticRung (tacSrc : String) (stmt : Expr) : MetaM (Option Expr) := do
  let r ← attempt <| forallTelescope stmt fun xs body => do
    match Parser.runParserCategory (← getEnv) `term s!"by {tacSrc}" with
    | .error _ => return none
    | .ok stx =>
      let savedMsgs := (← getThe Core.State).messages
      let res ← try
          let e ← Term.TermElabM.run' <| Term.withoutErrToSorry do
            let e ← Term.elabTerm stx (some body)
            Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e
          if e.hasSorry || e.hasMVar then pure none
          else pure (some (← mkLambdaFVars xs e))
        catch _ => pure none
      modifyThe Core.State fun st => { st with messages := savedMsgs }
      return res
  return r.join

/-- The hunt: refute first (cheap, and it kills the treadmill of spending
proof effort on falsehoods), then the proof ladder. -/
def hunt (known : Array KnownLemma) (corpusLemmas : Array Name) (stmt : Expr) :
    MetaM Verdict := do
  if let some cex ← tryRefute stmt then
    return .refuted cex
  if let some pf ← tryRefl stmt then
    return .proved pf "refl"
  if let some (pf, nm) ← tryKnown known stmt then
    return .proved pf "known" nm
  if let some (pf, nm) ← tryKnownSymm known stmt then
    return .proved pf "known, symm" nm
  if corpusLemmas.size > 0 then
    if let some pf ← trySimpWith corpusLemmas false stmt then
      return .proved pf "simp[corpus]"
  if let some pf ← trySimpWith corpusLemmas true stmt then
    return .proved pf "simp"
  if let some pf ← tryTacticRung "omega" stmt then
    return .proved pf "omega"
  return .stillOpen

end Runtime
end Eureka
