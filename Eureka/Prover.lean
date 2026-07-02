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

/-- Rung 1: the two sides are definitionally equal (`=` or `↔`). -/
def tryRefl (stmt : Expr) : MetaM (Option Expr) := do
  let r ← attempt <| forallTelescope stmt fun xs body => do
      if let some (_, lhs, rhs) := body.eq? then
        unless ← withNewMCtxDepth (isDefEq lhs rhs) do return none
        return some (← mkLambdaFVars xs (← mkEqRefl lhs))
      if let some (lhs, rhs) := body.app2? ``Iff then
        unless ← withNewMCtxDepth (isDefEq lhs rhs) do return none
        return some (← mkLambdaFVars xs (← mkAppM ``Iff.refl #[lhs]))
      return none
  return r.join

/-- The relation shape of a statement body, for the grounding prefilter. -/
inductive RelKind where
  | eq
  | iff
  | other
  deriving BEq

/-- Prefilter key: binder count (hypotheses of an implication count, since
`forallTelescope` absorbs them), relation kind, and the head constants of
the two sides (for `=`/`↔`; the conclusion's own head otherwise). -/
def statementKey (stmt : Expr) :
    MetaM (Option (Nat × RelKind × Option Name × Option Name)) := do
  let r ← attempt <| forallTelescope stmt fun xs body => do
    if let some (_, lhs, rhs) := body.eq? then
      return some (xs.size, RelKind.eq, lhs.getAppFn.constName?, rhs.getAppFn.constName?)
    if let some (lhs, rhs) := body.app2? ``Iff then
      return some (xs.size, RelKind.iff, lhs.getAppFn.constName?, rhs.getAppFn.constName?)
    return some (xs.size, RelKind.other, body.getAppFn.constName?, none)
  return r.join

/-- A library lemma eligible as a grounding certificate. Lemmas with one
universe parameter are admitted instantiated at `Level.zero`. `head`/`head2`
are the two sides' head constants; matching on them is only a *pruning*
heuristic where safe — definitional grounding of invented predicates must
not prune on heads, since defeq there works by delta-unfolding. -/
structure KnownLemma where
  name : Name
  type : Expr
  levels : List Level
  binders : Nat
  rel : RelKind
  head : Option Name
  head2 : Option Name

/-- Collect the grounding pool: theorems under the given namespace prefixes
(at most one universe parameter, instantiated at zero), keyed for the
prefilter. -/
def collectKnown (prefixes : List Name) : MetaM (Array KnownLemma) := do
  let env ← getEnv
  let cands : Array (Name × Expr × List Level) :=
    env.constants.fold (init := #[]) fun acc n ci =>
      if prefixes.any (·.isPrefixOf n) then
        match ci with
        | .thmInfo t =>
          match t.levelParams with
          | [] => acc.push (n, t.type, [])
          | [u] => acc.push (n, t.type.instantiateLevelParams [u] [Level.zero], [Level.zero])
          | _ => acc
        | _ => acc
      else acc
  let mut out := #[]
  for (n, ty, levels) in cands do
    if let some (binders, rel, head, head2) ← statementKey ty then
      out := out.push { name := n, type := ty, levels, binders, rel, head, head2 }
  return out

/-- Rung 2: the conjecture is definitionally an existing library lemma. The
proof is that lemma — and the discovery is thereby *grounded*: it is an
alias, and the caller reports which. -/
def tryKnown (known : Array KnownLemma) (stmt : Expr) :
    MetaM (Option (Expr × Name)) := do
  let some (binders, rel, head, _) ← statementKey stmt | return none
  for k in known do
    if k.binders == binders && k.rel == rel && k.head == head then
      if ← defeqSafe k.type stmt then
        return some (mkConst k.name k.levels, k.name)
  return none

/-- Rung 2b: the conjecture is an existing library lemma *stated the other
way around* (`=` or `↔`). The proof is the lemma with `Eq.symm`/`Iff.symm`
applied pointwise. -/
def tryKnownSymm (known : Array KnownLemma) (stmt : Expr) :
    MetaM (Option (Expr × Name)) := do
  let r ← attempt <| forallTelescope stmt fun xs body => do
      if let some (_, lhs, rhs) := body.eq? then
        let symmStmt ← mkForallFVars xs (← mkEq rhs lhs)
        let some (pf, nm) ← tryKnown known symmStmt | return none
        let proof ← mkLambdaFVars xs (← mkEqSymm (mkAppN pf xs))
        return some (proof, nm)
      if let some (lhs, rhs) := body.app2? ``Iff then
        let symmStmt ← mkForallFVars xs (mkApp2 (mkConst ``Iff) rhs lhs)
        let some (pf, nm) ← tryKnown known symmStmt | return none
        let proof ← mkLambdaFVars xs (← mkAppM ``Iff.symm #[mkAppN pf xs])
        return some (proof, nm)
      return none
  return r.join

/-- One chaining candidate: try to close `∀ xs, lhs ↔ rhs` through known
lemma `k : ∀ ys, A ↔ B`, matching `B ≐ rhs` (or `A ≐ rhs` when `flip`),
proving the remaining `∀ xs, lhs ↔ mid` with `subProve`, and composing with
`Iff.trans`. -/
private def chainVia (k : KnownLemma) (flip : Bool)
    (xs : Array Expr) (lhs rhs : Expr)
    (subProve : Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  let (mvs, _, kbody) ← forallMetaTelescope k.type
  let some (ka, kb) := kbody.app2? ``Iff | return none
  let (matchSide, otherSide) := if flip then (ka, kb) else (kb, ka)
  unless ← isDefEq matchSide rhs do return none
  let mid ← instantiateMVars otherSide
  if mid.hasExprMVar then return none
  let kApp ← instantiateMVars (mkAppN (mkConst k.name k.levels) mvs)
  if kApp.hasExprMVar then return none
  let subStmt ← mkForallFVars xs (mkApp2 (mkConst ``Iff) lhs mid)
  let some h₁ ← subProve subStmt | return none
  let bridge ← if flip then mkAppM ``Iff.symm #[kApp] else pure kApp
  let proof ← mkLambdaFVars xs
    (← mkAppM ``Iff.trans #[mkAppN h₁ xs, bridge])
  return some proof

/-- Transitive grounding, one step deep: certify `∀ xs, lhs ↔ rhs` by
composing a `subProve`-provable step `lhs ↔ mid` with a known library
`iff` bridging `mid ↔ rhs`. The certificate names the bridging lemma.
This is what closes alias chains like
`is_loop_def ↔ M.Dep {e} ↔ M.IsLoop e` (via `Matroid.singleton_dep`). -/
def tryKnownChain (known : Array KnownLemma) (stmt : Expr)
    (subProve : Expr → MetaM (Option Expr)) :
    MetaM (Option (Expr × Name)) := do
  let r ← attempt <| forallTelescope stmt fun xs body => do
    let some (lhs, rhs) := body.app2? ``Iff | return none
    let rhsHead := rhs.getAppFn.constName?
    for k in known do
      if k.rel == RelKind.iff then
        -- prune on the head of the side we must match against `rhs`
        for flip in [false, true] do
          let matchHead := if flip then k.head else k.head2
          if matchHead != rhsHead then
            continue
          let res ← withNewMCtxDepth <|
            (attempt (chainVia k flip xs lhs rhs subProve))
          if let some (some proof) := res then
            return some (proof, k.name)
    return none
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
  -- Mathlib rungs: the tactics parse only when the ambient environment
  -- imports Mathlib, so these self-disable in dependency-free runs.
  if let some pf ← tryTacticRung "tauto" stmt then
    return .proved pf "tauto"
  if let some pf ← tryTacticRung "aesop" stmt then
    return .proved pf "aesop"
  return .stillOpen

end Runtime
end Eureka
