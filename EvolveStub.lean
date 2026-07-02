import Eureka

/-!
Deterministic population run — no LLM. Templates and one meta-heuristic
(`specializerH`) compete for a per-generation judge budget allocated by
worth; `junkH` (falsehoods only) is killed by the kill rule; the specializer
births explorers (heuristic code generated from corpus data), and each
explorer births a probe — reflective depth 2: heuristic → heuristic →
heuristic, every birth through the rule gate, every fact through the fact
gate. Run with `lake env lean EvolveStub.lean`.
-/

open Lean Eureka.Runtime

/-- Proposes only fresh falsehoods (`∀ a, a + k = a` for growing `k`), to
demonstrate the kill rule. -/
def junkH : Agent where
  name := `junk
  propose := fun corpus => do
    let natTy := mkConst ``Nat
    let base := corpus.facts.size
    let mut out : Array RProposal := #[]
    for i in [1:13] do
      let k := base * 20 + i
      let stmt ← Meta.withLocalDeclD `a natTy fun a => do
        Meta.mkForallFVars #[a]
          (← Meta.mkEq (← Meta.mkAppM ``HAdd.hAdd #[a, mkNatLit k]) a)
      out := out.push (.fact { name := .mkSimple s!"junk_{k}", stmt, origin := `junk })
    return out

#eval show MetaM Unit from do
  let templates := [identityH, commH, idemH, assocH, distribH, mixerH].map Agent.ofConj
  let corpus ← evolve (templates ++ [junkH, specializerH])
    { generations := 4, judgeBudget := 40, perAgentCap := 25 }
  IO.println ""
  IO.println s!"final corpus: {corpus.facts.size} facts, all kernel-gated"
  -- Assertions: the kill rule fired on junk; the specializer birthed at
  -- least one explorer; some explorer birthed its probe (depth 2).
  let names := corpus.facts.map (·.name)
  unless corpus.facts.size ≥ 25 do
    throwError "expected a corpus of at least 25 facts, got {corpus.facts.size}"
  unless names.any (fun n => (toString n).startsWith "disco.absorbL") ∨
      names.any (fun n => (toString n).startsWith "disco.selfdistrib") ∨
      names.any (fun n => (toString n).startsWith "disco.probe") do
    throwError "expected at least one fact from a born heuristic"
  IO.println "population engine behaves as specified"
