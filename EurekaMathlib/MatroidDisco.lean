import EurekaMathlib.Domain

/-!
# Matroid discovery proper

Template agents over the predicates extracted from the `Matroid` namespace
— nothing matroid-specific is hardcoded except the templates' shapes:

* `implicationsAgent` — `P X → Q X` for same-shape pairs;
* `exclusionsAgent`  — `P X → ¬ Q X`;
* `dualityAgent`     — `P M✶ X ↔ Q M X` (the Whitney-duality family: the
  conjecture shape the formal-disco baseline run could state but not prove);
* `singletonAgent`   — `P e ↔ Q {e}` bridging element and set predicates.

Run through the population engine (worth, budget, kill rule) with the
`Matroid` grounding pool, then LLM booth rounds on top. There is no
counterexample search in this domain: false conjectures land in `open`,
and the honest reading of `open` is "unrefuted and unproved".
-/

open Lean Meta

namespace Eureka
namespace Runtime

private def mkSingleton (α e : Expr) : MetaM Expr :=
  mkAppOptM ``Singleton.singleton
    #[some α, some (mkApp (mkConst ``Set [Level.zero]) α), none, some e]

/-- `∀ α M X, P M X → ¬ Q M X` for same-shape pairs. -/
def exclusionsAgent (carrier : Name) (preds : Array PredInfo) : Agent where
  name := `exclusions
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for P in preds do
      for Q in preds do
        if P.name != Q.name && P.shape == Q.shape then
          let stmt ← mkPredForall carrier P.shape fun M X => do
            mkArrow (← mkAppM P.name #[M, X]) (mkNot (← mkAppM Q.name #[M, X]))
          out := out.push (.fact
            { name := .mkSimple s!"{P.name.getString!}_excl_{Q.name.getString!}",
              stmt, origin := `exclusions })
    return out

/-- `∀ α M X, P M X → Q M X` for same-shape pairs, as an agent. -/
def implicationsAgent (carrier : Name) (preds : Array PredInfo) : Agent where
  name := `implications
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for P in preds do
      for Q in preds do
        if P.name != Q.name && P.shape == Q.shape then
          out := out.push (.fact (← mkImplConjecture carrier P Q))
    return out

/-- `∀ α M X, P M✶ X ↔ Q M X` over same-shape pairs (`P = Q` allowed:
self-duality is a real question). -/
def dualityAgent (preds : Array PredInfo) : Agent where
  name := `duality
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for P in preds do
      for Q in preds do
        if P.shape == Q.shape then
          let stmt ← mkPredForall `Matroid P.shape fun M X => do
            let dualM ← mkAppM ``Matroid.dual #[M]
            return mkApp2 (mkConst ``Iff)
              (← mkAppM P.name #[dualM, X]) (← mkAppM Q.name #[M, X])
          out := out.push (.fact
            { name := .mkSimple s!"dual_{P.name.getString!}_{Q.name.getString!}",
              stmt, origin := `duality })
    return out

/-- `∀ α M e, P M e ↔ Q M {e}` for element predicate `P`, set predicate `Q`. -/
def singletonAgent (preds : Array PredInfo) : Agent where
  name := `singleton
  propose := fun _ => do
    let mut out : Array RProposal := #[]
    for P in preds do
      for Q in preds do
        if P.shape == PredShape.element && Q.shape == PredShape.set then
          let stmt ← withLocalDeclD `α (mkSort (.succ .zero)) fun α => do
            let carrierTy := mkApp (mkConst `Matroid [Level.zero]) α
            withLocalDeclD `M carrierTy fun M =>
              withLocalDeclD `e α fun e => do
                let sing ← mkSingleton α e
                mkForallFVars #[α, M, e] <| mkApp2 (mkConst ``Iff)
                  (← mkAppM P.name #[M, e]) (← mkAppM Q.name #[M, sing])
          out := out.push (.fact
            { name := .mkSimple s!"sing_{P.name.getString!}_{Q.name.getString!}",
              stmt, origin := `singleton })
    return out

/-- Booth prompt for the matroid domain. -/
def renderMatroidPrompt (preds : Array PredInfo)
    (corpus : Corpus) (lastRound : Option BoothLog) (perRound : Nat) :
    MetaM String := do
  let mut facts := ""
  for f in corpus.facts do
    facts := facts ++ s!"  {toString (← ppExpr f.stmt)}\n"
  let predList := String.intercalate ", " (preds.toList.map (·.name.toString))
  let feedback := match lastRound with
    | some log => s!"\nResults of your previous round:\n{renderLog log}"
    | none => ""
  return s!"You are the proposer in a verified discovery system exploring matroid \
theory in Lean 4 with Mathlib.

Established corpus:
{facts}{feedback}
Available predicates: {predList} (also `Matroid.dual` — `M✶` — and set
operations on `Set α`).

Propose {perRound} NEW conjectures about matroids that:
- are plausibly TRUE for all matroids (they are proof-searched and \
kernel-checked; there is no counterexample search, so false conjectures \
waste proof effort and land as 'open'),
- are not in the corpus and not trivial restatements,
- connect predicates the corpus does not yet connect (duality, complements, \
unions, the ground set M.E).

Output format — one conjecture per line, a bare Lean 4 term, nothing else:
∀ (α : Type) (M : Matroid α) (X : Set α), <statement>
or with (e : α) for element statements. Use full names (Matroid.Indep, \
M.IsBase, M✶, Set α). No prose, no numbering, no code fences."

end Runtime
end Eureka
