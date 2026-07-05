import Eureka.Reflect
import Eureka.Worth

/-!
# The population: worth, budget, birth, death

The EURISKO layer. Heuristics — template and born alike — live in one
population as `Agent`s. Any agent may propose facts, *new heuristics as
source code* (`RProposal.rule`) — so heuristics birth heuristics to any
depth — or *concepts* (`RProposal.concept`), mirroring the model's three
proposal kinds. Births pass the rule gate, facts pass the fact gate,
concepts pass the birth gate and the identity probe.

Worth (DESIGN_WORTH) is a fold of the event ledger through the pricing
table (`Eureka.Worth`): smoothed value per unit of attention, certainty
paid over novelty, children's value at `childFactor`, alias-farming
priced out by per-target decay. Each generation spends a judge budget in
worth order, with an exploration floor — every live agent gets one
judged proposal per generation before the shared budget applies (W3), so
starvation above the floor is a priced choice and the kill rule gets the
trials it needs. Agents with enough attention and negligible worth are
killed. Worth only decides *attention*: no pricing change can affect
what the gates admit (W4 — `discovery_sound` quantifies over adversarial
interpreters, which subsumes every schedule).
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- What an agent may propose: a fact, a new heuristic as source code, or
a concept — the model's three proposal kinds. -/
inductive RProposal where
  | fact (c : Conjecture)
  | rule (name : Name) (src : String)
  | concept (p : ConceptProposal)

/-- The agent interface type for born heuristics. -/
abbrev AgentFn := Corpus → MetaM (Array RProposal)

/-- A member of the population. `proposeP`, when present, supersedes
`propose` and additionally sees the concept pool (DESIGN_INVENT C3:
compounding agents must see tombstones and depths; the reflective agent
interface `AgentFn` stays untouched). -/
structure Agent where
  name : Name
  propose : AgentFn
  proposeP : Option (ConceptPool → Corpus → MetaM (Array RProposal)) := none
  parent : Option Name := none

/-- Wrap a facts-only heuristic as an agent. -/
def Agent.ofConj (h : ConjHeuristic) : Agent where
  name := h.name
  propose := fun c => return (← h.propose c).map .fact

private def fmtW (x : Float) : String :=
  let n := (x * 100).round.toUInt32.toNat
  s!"{n / 100}.{n % 100 / 10}{n % 10}"

private def agentFnType : MetaM Expr :=
  mkArrow (mkConst ``Corpus)
    (mkApp (mkConst ``MetaM) (mkApp (mkConst ``Array [Level.zero]) (mkConst ``RProposal)))

private unsafe def evalAgentFnUnsafe (e : Expr) : MetaM AgentFn := do
  Meta.evalExpr AgentFn (← agentFnType) e

@[implemented_by evalAgentFnUnsafe]
opaque evalAgentFn (e : Expr) : MetaM AgentFn

/-- The rule gate for agents: elaborate at the agent interface (falling back
to the facts-only interface for simpler proposers), policy-check, compile. -/
def installAgentSrc (name : Name) (src : String) (parent : Option Name := none) :
    MetaM (Except String Agent) := do
  match ← elabTermAt (← agentFnType) src with
  | .ok e =>
    if let some violation := rulePolicy e then
      return .error s!"rule policy violation: {violation}"
    return .ok { name, propose := ← evalAgentFn e, parent }
  | .error eAgent =>
    -- Fall back to the facts-only interface.
    match ← elabTermAt (← proposeFnType) src with
    | .ok e =>
      if let some violation := rulePolicy e then
        return .error s!"rule policy violation: {violation}"
      let fn ← evalProposeFn e
      return .ok { name, propose := fun c => return (← fn c).map .fact, parent }
    | .error _ => return .error eAgent

structure EvolveConfig where
  generations : Nat := 4
  judgeBudget : Nat := 40
  perAgentCap : Nat := 25
  minTrials : Nat := 10
  killThreshold : Float := 0.05
  knownPrefixes : List Name := [`Nat]
  /-- Domain refuter passed to `judge`; silent by default. -/
  refuter : Refuter := fun _ => pure none
  /-- The pricing table (DESIGN_WORTH W2). -/
  prices : Prices := {}
  /-- The exploration floor (W3): each live agent gets one judged proposal
  per generation before the shared budget applies. -/
  explorationFloor : Bool := true
  /-- Concept routing (W5): the probe context for `commitConcept` +
  `probeConcept`. Concept proposals are refused when absent. -/
  probeCtx : Option ProbeCtx := none
  /-- Canonical probe targets for the identity probe. -/
  canonical : Array ProbeTarget := #[]

/-- The population run's full result: the corpus, the event ledger (the
economy's instrument), the concept pool, and the final population. -/
structure EvolveResult where
  corpus : Corpus
  ledger : Ledger
  pool : ConceptPool
  population : Array Agent
  dead : Array Name

/-- Run the population. Every fact still enters through `commitFact`,
every heuristic birth through the rule gate, every concept through the
birth gate. Worth only decides *attention*. -/
def evolveWith (initial : List Agent) (cfg : EvolveConfig := {})
    (seed : Corpus := {}) (seedPool : ConceptPool := {}) : MetaM EvolveResult := do
  let known ← collectKnown cfg.knownPrefixes
  let mut corpus := seed
  let mut attempted : Array (Expr × Name) :=
    corpus.facts.map fun f => (f.stmt, f.name)
  let mut population : Array Agent := initial.toArray
  let mut ledger : Ledger := {}
  let mut pool : ConceptPool := seedPool
  let mut dead : Std.HashSet Name := {}
  for gen in [1 : cfg.generations + 1] do
    IO.println ""
    IO.println s!"── generation {gen} ──"
    let pop := population
    let children := fun (a : Name) =>
      (pop.filter (fun x => x.parent == some a)).map (·.name)
    let wor := fun (a : Name) => ledger.worth cfg.prices children a
    let live := population.filter fun a => !dead.contains a.name
    let ordered := live.qsort fun a b => wor a.name > wor b.name
    IO.println <| "  agenda: " ++ String.intercalate " · "
      (ordered.toList.map fun a => s!"{a.name} {fmtW (wor a.name)}")
    let mut budget := cfg.judgeBudget
    let mut starved : Array Name := #[]
    for agent in ordered do
      let mut floorLeft := if cfg.explorationFloor then 1 else 0
      if budget == 0 && floorLeft == 0 then
        starved := starved.push agent.name
        continue
      let fire := match agent.proposeP with
        | some f => f pool corpus
        | none => agent.propose corpus
      let some proposals ← attempt fire
        | IO.println s!"  [{agent.name}] crashed when fired"; continue
      let proposals := proposals.toList.take cfg.perAgentCap
      for p in proposals do
        match p with
        | .rule childName src =>
          if population.any (·.name == childName) then
            continue -- already born; silent (agents re-fire every generation)
          match ← installAgentSrc childName src (parent := agent.name) with
          | .ok child =>
            population := population.push child
            ledger := ledger.record agent.name .ruleBorn
            IO.println s!"  ✚ [{agent.name}] birthed heuristic {childName} (rule gate passed)"
          | .error e =>
            IO.println s!"  ✗ [{agent.name}] birth of {childName} refused: {e}"
        | .concept cp =>
          match cfg.probeCtx with
          | none =>
            ledger := ledger.record agent.name .conceptRefused
            IO.println s!"  ! [{agent.name}] concept {cp.name} — no concept gate configured"
          | some ctx =>
            if (← getEnv).contains (inventedNs ++ cp.name) then
              continue -- already born; silent (agents re-fire every generation)
            match ← commitConcept pool { cp with origin := agent.name } with
            | .error reason =>
              ledger := ledger.record agent.name .conceptRefused
              IO.println s!"  ! [{agent.name}] concept {cp.name} refused at birth: {reason}"
            | .ok (pool', c) =>
              pool := pool'
              let (pool'', corpus', verdict) ← withCurrHeartbeats <|
                probeConcept ctx pool corpus c cfg.canonical
              pool := pool''
              corpus := corpus'
              match verdict with
              | .aliasOf t _ _ =>
                ledger := ledger.record agent.name (.conceptAlias t false)
                IO.println s!"  ≡ [{agent.name}] {c.name} — {verdict.describe}"
              | .degenerate _ _ =>
                ledger := ledger.record agent.name .conceptDegenerate
                IO.println s!"  ⊥ [{agent.name}] {c.name} — {verdict.describe}"
              | .novel spec genl =>
                ledger := ledger.record agent.name .conceptNovel
                -- certified structure about the concept pays its inventor
                for _ in spec do
                  ledger := ledger.record agent.name (.inventedEdge c.name)
                for _ in genl do
                  ledger := ledger.record agent.name (.inventedEdge c.name)
                IO.println s!"  ✦ [{agent.name}] {c.name} — {verdict.describe}"
        | .fact c =>
          if attempted.any (fun q => q.1 == c.stmt) then
            ledger := ledger.record agent.name .factRepeat -- re-firing; free
            continue
          let mut alias? : Option Name := none
          for (a, nm) in attempted do
            if ← defeqSafe a c.stmt then
              alias? := some nm
              break
          if let some nm := alias? then
            ledger := ledger.record agent.name .factDup
            attempted := attempted.push (c.stmt, nm)
            IO.println s!"  ≡ [{agent.name}] {toString (← ppExpr c.stmt)} — alias of {nm}, merged"
            continue
          if floorLeft > 0 then
            floorLeft := floorLeft - 1  -- the exploration floor pays
          else if budget > 0 then
            budget := budget - 1
          else
            continue
          attempted := attempted.push (c.stmt, c.name)
          let pretty := toString (← ppExpr c.stmt)
          -- Conjectures in invented vocabulary go through the concept-aware
          -- judge: `judge`'s hunt sees invented constants as opaque.
          let mentionsInvented := pool.concepts.any fun cc =>
            c.stmt.getUsedConstants.contains cc.name
          let (corpus', outcome) ←
            match cfg.probeCtx, mentionsInvented with
            | some ctx, true => judgeConceptFact ctx corpus c cfg.refuter
            | _, _ => judge known corpus c cfg.refuter
          corpus := corpus'
          match outcome with
          | .refuted cex =>
            ledger := ledger.record agent.name .factRefuted
            IO.println s!"  ✗ [{agent.name}] {pretty} — refuted ({cex})"
          | .stillOpen =>
            ledger := ledger.record agent.name .factOpen
            IO.println s!"  ? [{agent.name}] {pretty} — open"
          | .admitted f note =>
            ledger := ledger.record agent.name .factAdmitted
            IO.println s!"  ✓ [{agent.name}] {pretty} — admitted ({note})"
            -- Facts in invented vocabulary pay the concepts' inventors;
            -- a fact linking two inventions re-probes the pair (D3
            -- trigger (i)) — a merge is delayed credit to the inventor.
            let used := f.stmt.getUsedConstants
            let mentioned := pool.concepts.filter fun cc => used.contains cc.name
            for cc in mentioned do
              ledger := ledger.record cc.origin (.inventedEdge cc.name)
            if mentioned.size ≥ 2 then
              if let some ctx := cfg.probeCtx then
                let (pool', corpus'', merges) ←
                  reprobeOnFact ctx pool corpus f
                pool := pool'
                corpus := corpus''
                for (younger, elder) in merges do
                  let origin := ((pool.find? younger).map (·.origin)).getD .anonymous
                  ledger := ledger.record origin (.conceptAlias elder true)
                  IO.println s!"  ≡ re-probe merged {younger} into {elder} \
(delayed credit to {origin})"
          | .refusedAtGate =>
            ledger := ledger.record agent.name .refusedAtGate
            IO.println s!"  ! [{agent.name}] {pretty} — evidence REFUSED by the gate"
    unless starved.isEmpty do
      IO.println s!"  budget exhausted — starved: {starved.toList}"
    -- kill sweep
    let pop' := population
    let children' := fun (a : Name) =>
      (pop'.filter (fun x => x.parent == some a)).map (·.name)
    for a in population do
      if !dead.contains a.name then
        let att := ledger.attention a.name
        let w := ledger.worth cfg.prices children' a.name
        if att ≥ cfg.minTrials && w < cfg.killThreshold then
          dead := dead.insert a.name
          IO.println s!"  † {a.name} killed (worth {fmtW w} after {att} attention)"
  IO.println ""
  IO.println "population (final):"
  let popF := population
  let childrenF := fun (a : Name) =>
    (popF.filter (fun x => x.parent == some a)).map (·.name)
  for a in population do
    let mark := if dead.contains a.name then " †" else ""
    let from_ := match a.parent with
      | some p => s!" (born of {p})"
      | none => ""
    IO.println s!"  {a.name}{mark}: worth \
{fmtW (ledger.worth cfg.prices childrenF a.name)} — \
{(ledger.counts a.name).describe}{from_}"
  return { corpus, ledger, pool, population,
           dead := population.filterMap fun a =>
             if dead.contains a.name then some a.name else none }

/-- `evolveWith`, corpus only. -/
def evolve (initial : List Agent) (cfg : EvolveConfig := {})
    (seed : Corpus := {}) : MetaM Corpus := do
  return (← evolveWith initial cfg seed).corpus

/-!
## A template meta-heuristic

`specializerH` reads the corpus and births a focused explorer for each
operation that already has admitted facts — heuristic code generated from
data. Each explorer, when fired, births a further probe (`probeSourceFor`),
so the chain specializer → explorer → probe exercises reflective depth 2
with no LLM in the loop.
-/

/-- Source for a depth-2 probe: `op (op a a) b = op a b` (collapses under
idempotence; false for e.g. addition — the gate decides). -/
def probeSourceFor (tag : String) (head : Name) : String :=
  s!"fun _corpus => do
  let natTy := mkConst ``Nat
  let stmt ← withLocalDeclD `a natTy fun a =>
    withLocalDeclD `b natTy fun b => do
      let aa ← mkAppM ``{head} #[a, a]
      let lhs ← mkAppM ``{head} #[aa, b]
      let rhs ← mkAppM ``{head} #[a, b]
      mkForallFVars #[a, b] (← mkEq lhs rhs)
  return #[RProposal.fact \{ name := `probe_{tag}_law, stmt, origin := `probe_{tag} }]"

/-- Source for an explorer of one operation: absorption and
self-distributivity laws, plus the birth of its probe. -/
def explorerSourceFor (tag : String) (head : Name) : String :=
  s!"fun _corpus => do
  let natTy := mkConst ``Nat
  let mut out : Array RProposal := #[]
  let absorbL ← withLocalDeclD `a natTy fun a =>
    withLocalDeclD `b natTy fun b => do
      let ab ← mkAppM ``{head} #[a, b]
      mkForallFVars #[a, b] (← mkEq (← mkAppM ``{head} #[a, ab]) ab)
  out := out.push (.fact \{ name := `absorbL_{tag}, stmt := absorbL, origin := `explore_{tag} })
  let selfDistrib ← withLocalDeclD `a natTy fun a =>
    withLocalDeclD `b natTy fun b =>
      withLocalDeclD `c natTy fun c => do
        let bc ← mkAppM ``{head} #[b, c]
        let ab ← mkAppM ``{head} #[a, b]
        let ac ← mkAppM ``{head} #[a, c]
        mkForallFVars #[a, b, c]
          (← mkEq (← mkAppM ``{head} #[a, bc]) (← mkAppM ``{head} #[ab, ac]))
  out := out.push (.fact \{ name := `selfdistrib_{tag}, stmt := selfDistrib, origin := `explore_{tag} })
  out := out.push (.rule `probe_{tag} (probeSourceFor \"{tag}\" ``{head}))
  return out"

/-- The meta-heuristic: birth an explorer for every operation the corpus
already knows something about. -/
def specializerH : Agent where
  name := `specializer
  propose := fun corpus => do
    let mut out : Array RProposal := #[]
    for op in opPool do
      let mentioned := corpus.facts.any fun f =>
        f.stmt.getUsedConstants.contains op.head
      if mentioned then
        out := out.push (.rule (.mkSimple s!"explore_{op.tag}")
          (explorerSourceFor op.tag op.head))
    return out

/-- The LLM as a member of the population: an agent whose only move is to
birth heuristics. Its children's discoveries pay it worth via parent
credit; if its heuristics are duds, it sinks on the agenda like anyone
else. -/
def llmOracleAgent (call : String → IO (Except String String)) : Agent where
  name := `llm_oracle
  propose := fun corpus => do
    let prompt ← renderRulePrompt corpus none
    match ← call prompt with
    | .error e =>
      IO.println s!"  [llm_oracle] call failed: {e}"
      return #[]
    | .ok text =>
      let src := extractTerm text
      return #[.rule (.mkSimple s!"llmborn_{corpus.facts.size}") src]

end Runtime
end Eureka
