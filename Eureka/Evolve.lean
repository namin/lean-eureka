import Eureka.Reflect
import Eureka.NL
import Eureka.Curator
import Eureka.Worth
import Eureka.Prove

/-!
# The population: worth, budget, birth, death

The EURISKO layer. Heuristics — template and born alike — live in one
population as `Agent`s. Any agent may propose facts, *new heuristics as
source code* (`RProposal.rule`) — so heuristics birth heuristics to any
depth — *new heuristics as English* (`RProposal.nlRule`,
DESIGN_HEURISTICS_NL: the body is data, fired by the trusted `nlAgent`
combinator through one metered LLM call), or *concepts*
(`RProposal.concept`). Births pass the rule gate (code) or the NL gate
(English), facts pass the fact gate, concepts pass the birth gate and
the identity probe.

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

/-- What an agent may propose: a fact, a new heuristic as source code, a
concept, or a new heuristic as English. The model needs no fourth kind:
`discovery_sound` quantifies over arbitrary adversarial interpreters, and
an LLM interpreting an English body is one instantiation of `.rule`'s
"arbitrary heuristic under an arbitrary interpreter". -/
inductive RProposal where
  | fact (c : Conjecture)
  | rule (name : Name) (src : String)
  | concept (p : ConceptProposal)
  /-- A heuristic birth as English (DESIGN_HEURISTICS_NL N1): the body is
  data, never elaborated or executed; the trusted combinator `nlAgent`
  interprets it at fire time through one metered LLM call. -/
  | nlRule (name : Name) (body : String)

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
  /-- NL heuristics (DESIGN_HEURISTICS_NL N1): the English body — data
  for the NL gate's dedup; never executed. -/
  nlBody : Option String := none
  /-- Firing this agent consumes one LLM call: metered per generation by
  `nlProposeBudget` and priced as `.llmCalled` attention (N4). -/
  llmPerFire : Bool := false

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

/-- The NL combinator (DESIGN_HEURISTICS_NL N1): the trusted interpreter
of a born English body. Renders the body into a stage-one-booth prompt,
makes ONE LLM call, parses the reply through the booth pipeline, and
returns `.fact` proposals. The body is never executed — the rule gate's
denylist question ("what may this code reach?") does not apply to it;
instead the loop meters the call (`nlProposeBudget`) and the ledger
prices it (`.llmCalled`). Unparseable reply lines are fed back into the
agent's next prompt, booth-style, not priced individually (N3). -/
def nlAgent (call : String → IO (Except String String)) (name : Name)
    (body : String) (parent : Option Name := none) : MetaM Agent := do
  let feedback ← IO.mkRef (none : Option String)
  let counter ← IO.mkRef 0
  let propose : AgentFn := fun corpus => do
    let prompt ← renderNLPrompt body corpus (← feedback.get)
    match ← call prompt with
    | .error e =>
      IO.println s!"  [{name}] LLM call failed: {e}"
      return #[]
    | .ok text =>
      let mut out : Array RProposal := #[]
      let mut bad : Array String := #[]
      for cand in extractCandidates text do
        match ← parseConjecture cand with
        | none => bad := bad.push cand
        | some stmt =>
          let i ← counter.get
          counter.set (i + 1)
          out := out.push (.fact
            { name := .mkSimple s!"{name}_{i}", stmt, origin := name })
      feedback.set (if bad.isEmpty then none else some
        (String.intercalate "\n" ((bad.toList.take 8).map fun l => s!"  {l}")))
      return out
  return { name, parent, propose, nlBody := some body, llmPerFire := true }

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
  /-- Escalation (DESIGN_DEPTH P1/P5): open conjectures re-judged per
  generation with the deep ladder — a system budget, deliberately not
  worth-ordered. 0 = off. -/
  escalationBudget : Nat := 0
  /-- The deep ladder's configuration (widened pool, uncut rungs, deeper
  composition). Escalation is inert without it. -/
  deepCtx : Option ProbeCtx := none
  /-- LLM proof transport (DESIGN_PROVE V1/V4): when present, an open
  conjecture that survives symbolic escalation gets a repair-loop
  attempt, metered by `llmProofBudget` calls per generation. -/
  proofCall : Option (String → IO (Except String String)) := none
  llmProofBudget : Nat := 0
  /-- The in-loop sweep (DESIGN_INVENT D3-ii, wired by DESIGN_RECORD R4):
  per-generation re-probe budget over unmerged pairs, cursor carried
  across generations — the standing-obligation tail trigger (i) cannot
  reach. 0 = off. -/
  sweepBudget : Nat := 0
  /-- NL heuristics (DESIGN_HEURISTICS_NL N2): the transport for `.nlRule`
  births. Births are refused when absent, mirroring concept routing. -/
  nlCall : Option (String → IO (Except String String)) := none
  /-- N4: LLM firings per generation across `llmPerFire` agents, spent in
  worth order like the judge budget. 0 = such agents never fire. -/
  nlProposeBudget : Nat := 0
  /-- The curator (DESIGN_CURATOR L8): transport for the curate pass.
  Absent = no curation. -/
  curatorCall : Option (String → IO (Except String String)) := none
  /-- Curate calls per generation (a system budget, like escalation). -/
  curatorBudget : Nat := 1
  /-- Genome-backed agents the mutation stream may start from (L4). -/
  seedGenomes : List (Name × MutGenome) := []
  /-- Curator-less mutation pressure (L7-iv baseline): mutants birthed
  per generation by round-robin over the genome table. 0 = off. -/
  mutationRoundRobin : Nat := 0

/-- The population run's full result: the corpus, the event ledger (the
economy's instrument), the concept pool, the final population, and the
open set — the standing worklist (and the benchmark generator's
output, DESIGN_RECORD R2). -/
structure EvolveResult where
  corpus : Corpus
  ledger : Ledger
  pool : ConceptPool
  population : Array Agent
  dead : Array Name
  opens : Array (Conjecture × Name × Nat) := #[]
  /-- Curator labels (DESIGN_CURATOR L1): display-layer notes. -/
  labels : Array (Name × String) := #[]

/-- Merges pay through one path (DESIGN_RECORD R3): delayed-alias credit
to the younger concept's inventor, attracted credit to the elder's when
distinct. Used by trigger (i) and the sweep alike. -/
private def creditMerges (pool : ConceptPool) (ledger : Ledger)
    (merges : Array (Name × Name)) (how : String) : MetaM Ledger := do
  let mut ledger := ledger
  for (younger, elder) in merges do
    let origin := ((pool.find? younger).map (·.origin)).getD .anonymous
    ledger := ledger.record origin (.conceptAlias elder true)
    if let some ec := pool.find? elder then
      if ec.origin != origin then
        ledger := ledger.record ec.origin (.conceptAttracted elder)
    IO.println s!"  ≡ {how} merged {younger} into {elder} \
(delayed credit to {origin})"
  return ledger

/-- The one credit path for an admitted fact (R3): mentioned concepts pay
their inventors; a fact linking two live inventions fires re-probe
trigger (i); trigger merges pay through `creditMerges`. -/
private def creditAdmission (probeCtx : Option ProbeCtx)
    (pool : ConceptPool) (corpus : Corpus) (ledger : Ledger) (f : Fact) :
    MetaM (ConceptPool × Corpus × Ledger) := do
  let used := f.stmt.getUsedConstants
  let mentioned := pool.concepts.filter fun cc => used.contains cc.name
  let mut ledger := ledger
  let mut pool := pool
  let mut corpus := corpus
  for cc in mentioned do
    ledger := ledger.record cc.origin (.inventedEdge cc.name)
  if mentioned.size ≥ 2 then
    if let some ctx := probeCtx then
      let (pool', corpus', merges) ← reprobeOnFact ctx pool corpus f
      pool := pool'
      corpus := corpus'
      ledger ← creditMerges pool ledger merges "re-probe"
  return (pool, corpus, ledger)

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
  -- The open set (P1): conjectures judged open, kept for escalation —
  -- (conjecture, proposer, escalation tries).
  let mut opens : Array (Conjecture × Name × Nat) := #[]
  let mut sweepCursor := 0
  -- Curator + mutation state (DESIGN_CURATOR): the genome table, fact
  -- provenance for flags, the one-flag-per-fact set, escalation
  -- nominations, labels, and the mutation cursor.
  let mut genomes : NameMap MutGenome :=
    cfg.seedGenomes.foldl (fun m (n, g) => m.insert n g) {}
  let mut factOrigins : NameMap (Name × Tier) := {}
  let mut flagged : NameSet := {}
  let mut nominated : Array Name := #[]
  let mut labels : Array (Name × String) := #[]
  let mut mutCursor := 0
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
    let mut nlBudget := cfg.nlProposeBudget
    let mut starved : Array Name := #[]
    let mut genLog : Array String := #[]
    for agent in ordered do
      let mut floorLeft := if cfg.explorationFloor then 1 else 0
      if budget == 0 && floorLeft == 0 then
        starved := starved.push agent.name
        continue
      -- Metered firing (DESIGN_HEURISTICS_NL N4): an `llmPerFire` agent's
      -- firing is one LLM call — spent from `nlBudget` in worth order and
      -- priced as attention, whatever the call returns.
      if agent.llmPerFire then
        if nlBudget == 0 then
          starved := starved.push agent.name
          continue
        nlBudget := nlBudget - 1
        ledger := ledger.record agent.name .llmCalled
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
        | .nlRule childName body =>
          if population.any (·.name == childName) then
            continue -- already born; silent (agents re-fire every generation)
          match cfg.nlCall with
          | none =>
            ledger := ledger.record agent.name .nlRefused
            IO.println s!"  ! [{agent.name}] NL heuristic {childName} — \
no NL transport configured"
          | some call =>
            match nlBodyCheck body (population.filterMap (·.nlBody)) with
            | some violation =>
              ledger := ledger.record agent.name .nlRefused
              IO.println s!"  ✗ [{agent.name}] NL birth of {childName} \
refused: {violation}"
            | none =>
              let child ← nlAgent call childName body (parent := agent.name)
              population := population.push child
              ledger := ledger.record agent.name .ruleBorn
              IO.println s!"  ✚ [{agent.name}] birthed NL heuristic \
{childName} (NL gate passed)"
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
                -- The bridge landed on an invented target: its inventor
                -- is paid attracted credit (P4), prober excluded.
                if let some cc := pool.find? t then
                  if cc.origin != agent.name then
                    ledger := ledger.record cc.origin (.conceptAttracted t)
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
            genLog := genLog.push s!"≡ [{agent.name}] {toString (← ppExpr c.stmt)} — alias of {nm}"
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
            genLog := genLog.push s!"✗ [{agent.name}] {pretty} — refuted ({cex})"
            IO.println s!"  ✗ [{agent.name}] {pretty} — refuted ({cex})"
          | .stillOpen =>
            ledger := ledger.record agent.name .factOpen
            opens := opens.push (c, agent.name, 0)
            genLog := genLog.push s!"? [{agent.name}] {pretty} — open"
            IO.println s!"  ? [{agent.name}] {pretty} — open"
          | .admitted f note =>
            ledger := ledger.record agent.name (.factAdmitted (tierOfRung note))
            factOrigins := factOrigins.insert f.name (agent.name, tierOfRung note)
            genLog := genLog.push s!"✓ [{agent.name}] {pretty} — admitted as {f.name} ({note})"
            IO.println s!"  ✓ [{agent.name}] {pretty} — admitted ({note})"
            let (pool', corpus'', ledger') ←
              creditAdmission cfg.probeCtx pool corpus ledger f
            pool := pool'
            corpus := corpus''
            ledger := ledger'
          | .refusedAtGate =>
            ledger := ledger.record agent.name .refusedAtGate
            IO.println s!"  ! [{agent.name}] {pretty} — evidence REFUSED by the gate"
    unless starved.isEmpty do
      IO.println s!"  budget exhausted — starved: {starved.toList}"
    -- Escalation pass (P1/P5): a system budget, invented-vocabulary
    -- statements first, at most 2 tries per conjecture. Successes pay the
    -- original proposer at the escalated tier; failures cost them an
    -- attention (deep attempts are spent on your behalf).
    if cfg.escalationBudget > 0 then
      if let some deep := cfg.deepCtx then
        let mentionsInv := fun (e : Conjecture × Name × Nat) =>
          pool.concepts.any fun cc => e.1.stmt.getUsedConstants.contains cc.name
        -- Breadth before retries: unattempted conjectures first (tries
        -- ascending), invented-vocabulary first within that — otherwise a
        -- stuck head-of-queue family starves the rest of the open set.
        let eligible := (opens.filter fun e => e.2.2 < 2).qsort
          fun a b => a.2.2 < b.2.2
        let queue := eligible.filter mentionsInv ++
          eligible.filter (fun e => !mentionsInv e)
        -- Curator nominations (DESIGN_CURATOR L5) jump the queue,
        -- consumed on use.
        let isNom := fun (e : Conjecture × Name × Nat) =>
          nominated.any (· == e.1.name)
        let queue := queue.filter isNom ++ queue.filter (fun e => !isNom e)
        nominated := #[]
        let mut attemptedStmts : Array Expr := #[]
        let mut resolvedStmts : Array Expr := #[]
        let mut llmLeft := cfg.llmProofBudget
        for (c, proposer, _) in queue do
          if attemptedStmts.size ≥ cfg.escalationBudget then break
          attemptedStmts := attemptedStmts.push c.stmt
          let (corpus', outcome') ← escalate deep corpus c cfg.refuter
          corpus := corpus'
          let mut outcome := outcome'
          -- The repair rung (V1/V4): after the symbolic ladder, metered.
          if let some call := cfg.proofCall then
            if llmLeft > 0 then
              if let .stillOpen := outcome then
                llmLeft := llmLeft - 1
                if let some (pf, _) ← proveByRepair call deep.known c.stmt then
                  let nm ← freshName c.name
                  if let some f ← commitFact { name := nm, stmt := c.stmt, proof := pf } then
                    corpus := { corpus with facts := corpus.facts.push f }
                    outcome := .admitted f "escalated: llm-repair"
          match outcome with
          | .admitted f note =>
            ledger := ledger.record proposer (.factAdmitted .escalated)
            factOrigins := factOrigins.insert f.name (proposer, .escalated)
            resolvedStmts := resolvedStmts.push c.stmt
            genLog := genLog.push s!"⇧ [{proposer}] {toString (← ppExpr c.stmt)} — \
admitted as {f.name} ({note})"
            IO.println s!"  ⇧ [{proposer}] {toString (← ppExpr c.stmt)} — \
admitted ({note})"
            let (pool', corpus'', ledger') ←
              creditAdmission cfg.probeCtx pool corpus ledger f
            pool := pool'
            corpus := corpus''
            ledger := ledger'
          | .refuted cex =>
            ledger := ledger.record proposer .factRefuted
            resolvedStmts := resolvedStmts.push c.stmt
            IO.println s!"  ⇧ [{proposer}] {toString (← ppExpr c.stmt)} — \
refuted ({cex})"
          | .stillOpen =>
            ledger := ledger.record proposer .factOpen
            IO.println s!"  ⇧ [{proposer}] {toString (← ppExpr c.stmt)} — \
still open after escalation"
          | .refusedAtGate => pure ()
        opens := opens.filterMap fun (c, pr, t) =>
          if resolvedStmts.any (· == c.stmt) then none
          else if attemptedStmts.any (· == c.stmt) then some (c, pr, t + 1)
          else some (c, pr, t)
    -- The in-loop sweep (R4): the identity obligation's tail.
    if cfg.sweepBudget > 0 then
      if let some ctx := cfg.probeCtx then
        let (pool', corpus', merges, cursor') ← sweepReprobe ctx pool corpus
          cfg.canonical cfg.sweepBudget sweepCursor
        pool := pool'
        corpus := corpus'
        sweepCursor := cursor'
        ledger ← creditMerges pool ledger merges "sweep"
    -- The mutation stream (DESIGN_CURATOR L4): requests from the
    -- round-robin baseline and from curator `mutate` actions, birthed
    -- below as ordinary rule-gate births with parent credit.
    let mut mutationRequests : Array (Name × MutGenome) := #[]
    if cfg.mutationRoundRobin > 0 then
      let entries := genomes.toList.toArray
      unless entries.isEmpty do
        let mut made := 0
        let mut tries := 0
        while made < cfg.mutationRoundRobin && tries < entries.size * 4 do
          let (tname, g) := entries[mutCursor % entries.size]!
          let op : MutOp := if tries % 2 == 0 then .substOp else .restrictPool
          mutCursor := mutCursor + 1
          tries := tries + 1
          if let some g' := applyMutOp g op mutCursor none then
            unless population.any (·.name == g'.mutName) do
              mutationRequests := mutationRequests.push (tname, g')
              made := made + 1
    -- The curate pass (DESIGN_CURATOR L1–L3, L5–L6): schedule-only by
    -- type. Runs before the kill sweep; every effect is a priced,
    -- bounded ledger event, a nomination, a mutation *choice*, or a
    -- label. The kill rule itself is untouched (L3).
    if let some ccall := cfg.curatorCall then
      let popNow := population
      let childrenNow := fun (a : Name) =>
        (popNow.filter (fun x => x.parent == some a)).map (·.name)
      let liveNow := population.filter fun a => !dead.contains a.name
      let mut agendaStr := ""
      for a in liveNow do
        agendaStr := agendaStr ++
          s!"  {a.name} {fmtW (ledger.worth cfg.prices childrenNow a.name)}\n"
      let outcomesStr := String.intercalate "\n"
        ((genLog.toList.take 60).map fun l => s!"  {l}") ++ "\n"
      let mut mutablesStr := ""
      for (n, g) in genomes.toList do
        mutablesStr := mutablesStr ++ s!"  {n}: schemas \
[{String.intercalate ", " (g.schemas.map (·.tag))}], ops \
[{String.intercalate ", " (g.ops.map (·.tag))}]\n"
      for _ in [0 : cfg.curatorBudget] do
        let prompt := renderCuratorPrompt gen agendaStr outcomesStr mutablesStr
        ledger := ledger.record `curator .llmCalled
        match ← ccall prompt with
        | .error e => IO.println s!"  [curator] call failed: {e}"
        | .ok text =>
          let (actions, dropped) := parseCuratorReply text
          for d in dropped do
            IO.println s!"  [curator] dropped: {d}"
          for act in actions do
            match act with
            | .boost a =>
              if population.any (·.name == a) then
                ledger := ledger.record a .curatorBoost
                IO.println s!"  [curator] ▲ boost {a}"
              else IO.println s!"  [curator] dropped boost: unknown agent {a}"
            | .damp a =>
              if population.any (·.name == a) then
                ledger := ledger.record a .curatorDamp
                IO.println s!"  [curator] ▼ damp {a}"
              else IO.println s!"  [curator] dropped damp: unknown agent {a}"
            | .flag f =>
              match factOrigins.find? f with
              | some (origin, tier) =>
                if flagged.contains f then
                  IO.println s!"  [curator] dropped flag: {f} already flagged"
                else
                  flagged := flagged.insert f
                  ledger := ledger.record origin (.curatorFlagged tier)
                  IO.println s!"  [curator] ⚑ {f} — admission pay \
cancelled for {origin}"
              | none => IO.println s!"  [curator] dropped flag: unknown fact {f}"
            | .escalate c =>
              nominated := nominated.push c
              IO.println s!"  [curator] ⇧ {c} nominated for escalation \
(next generation)"
            | .mutate t op =>
              match genomes.find? t with
              | some g =>
                let donor? := match op with
                  | .crossover d => genomes.find? d
                  | _ => none
                mutCursor := mutCursor + 1
                match applyMutOp g op mutCursor donor? with
                | some g' => mutationRequests := mutationRequests.push (t, g')
                | none =>
                  IO.println s!"  [curator] mutate {t}: operator not applicable"
              | none => IO.println s!"  [curator] dropped mutate: no genome for {t}"
            | .label t note =>
              labels := labels.push (t, note)
              IO.println s!"  [curator] ✎ {t}: {note}"
    for (tname, g') in mutationRequests do
      if population.any (·.name == g'.mutName) then continue
      match ← installAgentSrc g'.mutName (genomeSourceFor g') (parent := tname) with
      | .ok child =>
        population := population.push child
        genomes := genomes.insert g'.mutName g'
        ledger := ledger.record tname .ruleBorn
        IO.println s!"  ⚙ mutant {g'.mutName} born of {tname} (rule gate passed)"
      | .error e =>
        IO.println s!"  ✗ mutant {g'.mutName} refused: {e}"
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
  return { corpus, ledger, pool, population, opens, labels,
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

/-- The NL sibling of `llmOracleAgent` (DESIGN_HEURISTICS_NL N5): its
only move is to birth heuristics *as English*. Its own firing is
metered like every `llmPerFire` agent; duplicate or vacuous births are
refused by the NL gate and priced, and dud children sink it via parent
credit like anyone else. -/
def nlOracleAgent (call : String → IO (Except String String)) : Agent where
  name := `nl_oracle
  llmPerFire := true
  propose := fun corpus => do
    let prompt ← renderNLOraclePrompt corpus
    match ← call prompt with
    | .error e =>
      IO.println s!"  [nl_oracle] call failed: {e}"
      return #[]
    | .ok text =>
      return #[.nlRule (.mkSimple s!"nlborn_{corpus.facts.size}")
        text.trimAscii.toString]

end Runtime
end Eureka
