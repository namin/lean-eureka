import Eureka.Reflect

/-!
# The population: worth, budget, birth, death

The EURISKO layer. Heuristics — template and born alike — live in one
population as `Agent`s. Any agent may propose facts *or new heuristics as
source code* (`RProposal.rule`), so heuristics birth heuristics to any
depth; births pass the rule gate, facts pass the fact gate, exactly as in
the model (`admitRuleGated`). Worth is earned:

  worth = min 1 (admitRate × dupPenalty)
  admitRate  = (admitted + ½·childAdmitted + ½) / (judged + 1)
  dupPenalty = 1 − merged/(proposed + 1)

The duplication penalty makes synonym-tower behavior *unprofitable* — the
failure mode where worth credits duplicators, observed in
formal-disco-eurisko-verified, is priced in from the start. Parent credit
(`childAdmitted`) pays heuristic-writers for their children's discoveries,
so a productive meta-heuristic rises on the agenda. Each generation has a
judge budget spent in worth order — low-worth agents starve — and agents
with enough trials and negligible worth are killed.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- What an agent may propose: a fact, or a new heuristic as source code. -/
inductive RProposal where
  | fact (c : Conjecture)
  | rule (name : Name) (src : String)

/-- The agent interface type for born heuristics. -/
abbrev AgentFn := Corpus → MetaM (Array RProposal)

/-- A member of the population. -/
structure Agent where
  name : Name
  propose : AgentFn
  parent : Option Name := none

/-- Wrap a facts-only heuristic as an agent. -/
def Agent.ofConj (h : ConjHeuristic) : Agent where
  name := h.name
  propose := fun c => return (← h.propose c).map .fact

structure AgentStats where
  proposed : Nat := 0
  judged : Nat := 0
  admitted : Nat := 0
  refuted : Nat := 0
  merged : Nat := 0
  openCount : Nat := 0
  rulesBorn : Nat := 0
  childAdmitted : Nat := 0

def AgentStats.worth (s : AgentStats) : Float :=
  let eff := s.admitted.toFloat + 0.5 * s.childAdmitted.toFloat
  let admitRate := (eff + 0.5) / (s.judged.toFloat + 1.0)
  let dupPenalty := 1.0 - s.merged.toFloat / (s.proposed.toFloat + 1.0)
  min 1.0 (admitRate * dupPenalty)

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

/-- Run the population. Every fact still enters through `commitFact`; every
birth still enters through the rule gate. Worth only decides *attention*. -/
def evolve (initial : List Agent) (cfg : EvolveConfig := {})
    (seed : Corpus := {}) : MetaM Corpus := do
  let known ← collectKnown cfg.knownPrefixes
  let mut corpus := seed
  let mut attempted : Array (Expr × Name) :=
    corpus.facts.map fun f => (f.stmt, f.name)
  let mut population : Array Agent := initial.toArray
  let mut stats : Std.HashMap Name AgentStats := {}
  let mut dead : Std.HashSet Name := {}
  for gen in [1 : cfg.generations + 1] do
    IO.println ""
    IO.println s!"── generation {gen} ──"
    let live := population.filter fun a => !dead.contains a.name
    let ordered := live.qsort fun a b =>
      (stats.getD a.name {}).worth > (stats.getD b.name {}).worth
    IO.println <| "  agenda: " ++ String.intercalate " · "
      (ordered.toList.map fun a => s!"{a.name} {fmtW (stats.getD a.name {}).worth}")
    let mut budget := cfg.judgeBudget
    let mut starved : Array Name := #[]
    for agent in ordered do
      if budget == 0 then
        starved := starved.push agent.name
        continue
      let some proposals ← attempt (agent.propose corpus)
        | IO.println s!"  [{agent.name}] crashed when fired"; continue
      let proposals := proposals.toList.take cfg.perAgentCap
      let mut s := stats.getD agent.name {}
      s := { s with proposed := s.proposed + proposals.length }
      for p in proposals do
        match p with
        | .rule childName src =>
          if population.any (·.name == childName) then
            continue -- already born; silent (agents re-fire every generation)
          match ← installAgentSrc childName src (parent := agent.name) with
          | .ok child =>
            population := population.push child
            s := { s with rulesBorn := s.rulesBorn + 1 }
            IO.println s!"  ✚ [{agent.name}] birthed heuristic {childName} (rule gate passed)"
          | .error e =>
            IO.println s!"  ✗ [{agent.name}] birth of {childName} refused: {e}"
        | .fact c =>
          if attempted.any (fun q => q.1 == c.stmt) then
            s := { s with merged := s.merged + 1 } -- verbatim repeat; silent
            continue
          let mut alias? : Option Name := none
          for (a, nm) in attempted do
            if ← defeqSafe a c.stmt then
              alias? := some nm
              break
          if let some nm := alias? then
            s := { s with merged := s.merged + 1 }
            attempted := attempted.push (c.stmt, nm)
            IO.println s!"  ≡ [{agent.name}] {toString (← ppExpr c.stmt)} — alias of {nm}, merged"
            continue
          if budget == 0 then
            continue
          budget := budget - 1
          s := { s with judged := s.judged + 1 }
          attempted := attempted.push (c.stmt, c.name)
          let pretty := toString (← ppExpr c.stmt)
          let (corpus', outcome) ← judge known corpus c cfg.refuter
          corpus := corpus'
          match outcome with
          | .refuted cex =>
            s := { s with refuted := s.refuted + 1 }
            IO.println s!"  ✗ [{agent.name}] {pretty} — refuted ({cex})"
          | .stillOpen =>
            s := { s with openCount := s.openCount + 1 }
            IO.println s!"  ? [{agent.name}] {pretty} — open"
          | .admitted _ note =>
            s := { s with admitted := s.admitted + 1 }
            IO.println s!"  ✓ [{agent.name}] {pretty} — admitted ({note})"
            if let some p := agent.parent then
              let ps := stats.getD p {}
              stats := stats.insert p { ps with childAdmitted := ps.childAdmitted + 1 }
          | .refusedAtGate =>
            IO.println s!"  ! [{agent.name}] {pretty} — evidence REFUSED by the gate"
      stats := stats.insert agent.name s
    unless starved.isEmpty do
      IO.println s!"  budget exhausted — starved: {starved.toList}"
    -- kill sweep
    for a in population do
      if !dead.contains a.name then
        let s := stats.getD a.name {}
        if s.judged ≥ cfg.minTrials && s.worth < cfg.killThreshold then
          dead := dead.insert a.name
          IO.println s!"  † {a.name} killed (worth {fmtW s.worth} after {s.judged} judged)"
  IO.println ""
  IO.println "population (final):"
  for a in population do
    let s := stats.getD a.name {}
    let mark := if dead.contains a.name then " †" else ""
    let from_ := match a.parent with
      | some p => s!" (born of {p})"
      | none => ""
    IO.println s!"  {a.name}{mark}: worth {fmtW s.worth} — \
{s.admitted} admitted, {s.refuted} refuted, {s.merged} merged, \
{s.openCount} open, {s.rulesBorn} birthed, {s.childAdmitted} via children{from_}"
  return corpus

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
