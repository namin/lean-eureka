import Eureka.Concepts

/-!
# The worth ledger (DESIGN_WORTH W1–W2)

Worth decides *attention* — which proposals get judged, who starves, who
dies. Here it becomes a fold over an append-only ledger of typed events
through a pricing table: prices are data, so repricing is a table edit;
delayed credit (a re-probe merge paying the inventor generations later)
is an ordinary event; and worth trajectories — the economy's instrument
— are a projection of the ledger.

The pricing rulings (DESIGN_WORTH W2): pay certainty, not novelty. A
certified refutation pays strictly between an admission and an open
(settled knowledge is worth something; silence is not). A concept pays
nothing for being born novel — it earns when it generates certified
structure (bridges, edges, facts in its vocabulary), and alias-merges
decay per (agent × canonical target) so reinvention is not farmable.

None of this touches soundness: worth selects what gets judged, never
what gets admitted — `discovery_sound` quantifies over adversarial
interpreters, which subsumes every scheduling policy (W4).
-/

open Lean

namespace Eureka
namespace Runtime

/-- The event vocabulary. `delayed` on an alias marks credit landing after
birth (a re-probe merge): it pays, but consumes no attention — the agent
did not act. -/
inductive EventKind where
  | factAdmitted
  | factRefuted
  | factOpen
  /-- A verbatim re-proposal — the mechanical artifact of agents re-firing
  every generation. Filtered at zero cost, priced at zero. -/
  | factRepeat
  /-- A *new* statement that is definitionally an attempted one — genuine
  near-duplication, priced negatively. -/
  | factDup
  | refusedAtGate
  | ruleBorn
  | conceptAlias (target : Name) (delayed : Bool)
  | conceptDegenerate
  | conceptNovel
  | conceptRefused
  | inventedEdge (concept : Name)
  deriving BEq, Repr, Inhabited

structure Event where
  agent : Name
  kind : EventKind
  deriving Repr, Inhabited

/-- Append-only; provenance is the order. -/
structure Ledger where
  events : Array Event := #[]
  deriving Inhabited

def Ledger.record (l : Ledger) (agent : Name) (kind : EventKind) : Ledger :=
  { l with events := l.events.push ⟨agent, kind⟩ }

/-- The pricing table (DESIGN_WORTH W2). Initial values; the fit criterion
against the instruments (the separated economy experiment, the operator
derby) is fixed in the design, so adjusting these is an experiment, not a
redesign. -/
structure Prices where
  admitted : Float := 1.0
  refuted : Float := 0.5
  /-- Decaying returns on refutations: the n-th pays
  `refuted / (1 + n/refutedDecay)`. The first few refutations are real
  information (the economy experiment's demand); an agent producing
  *only* falsehoods sinks instead of plateauing — falsehood-farming is
  not a stable strategy. -/
  refutedDecay : Float := 4.0
  opened : Float := 0.0
  dup : Float := -0.25
  refused : Float := -0.5
  conceptAlias : Float := 0.75
  conceptDegenerate : Float := 0.25
  conceptNovel : Float := 0.0
  inventedEdge : Float := 1.0
  childFactor : Float := 0.5

/-- Does the event consume attention (a judge slot or a birth-gate pass)?
Proposal-time repeats and dups, delayed credits, and rule births do
not. -/
def EventKind.attention : EventKind → Bool
  | .factAdmitted | .factRefuted | .factOpen | .refusedAtGate => true
  | .conceptAlias _ delayed => !delayed
  | .conceptDegenerate | .conceptNovel | .conceptRefused => true
  | .factRepeat | .factDup | .ruleBorn | .inventedEdge _ => false

/-- An agent's own accumulated value — the fold that *is* the pricing:
alias decay per canonical target, decaying returns on refutations, both
in ledger order. -/
def Ledger.ownValue (l : Ledger) (p : Prices) (agent : Name) : Float :=
  Id.run do
    let mut paidTargets : Array Name := #[]
    let mut refutedSeen : Float := 0.0
    let mut v : Float := 0.0
    for e in l.events do
      if e.agent == agent then
        match e.kind with
        | .factAdmitted => v := v + p.admitted
        | .factRefuted =>
          v := v + p.refuted / (1.0 + refutedSeen / p.refutedDecay)
          refutedSeen := refutedSeen + 1.0
        | .factOpen => v := v + p.opened
        | .factRepeat => pure ()
        | .factDup => v := v + p.dup
        | .refusedAtGate => v := v + p.refused
        | .ruleBorn => pure ()
        | .conceptAlias t _ =>
          unless paidTargets.contains t do
            v := v + p.conceptAlias
            paidTargets := paidTargets.push t
        | .conceptDegenerate => v := v + p.conceptDegenerate
        | .conceptNovel => v := v + p.conceptNovel
        | .conceptRefused => v := v + p.refused
        | .inventedEdge _ => v := v + p.inventedEdge
    return v

def Ledger.attention (l : Ledger) (agent : Name) : Nat :=
  l.events.foldl
    (fun n e => if e.agent == agent && e.kind.attention then n + 1 else n) 0

/-- Worth: smoothed value per unit of attention, children's value included
at `childFactor` (one level — the generalization of the old
`childAdmitted`, refutations and concept credit included). -/
def Ledger.worth (l : Ledger) (p : Prices) (children : Name → Array Name)
    (agent : Name) : Float :=
  let own := l.ownValue p agent
  let kids := (children agent).foldl (fun v c => v + l.ownValue p c) 0.0
  let v := own + p.childFactor * kids
  min 1.0 (max 0.0 ((v + 0.5) / ((l.attention agent).toFloat + 1.0)))

/-- The old `AgentStats`, as a ledger projection — counts for reporting,
never for pricing. -/
structure AgentCounts where
  admitted : Nat := 0
  refuted : Nat := 0
  opens : Nat := 0
  dups : Nat := 0
  refused : Nat := 0
  rulesBorn : Nat := 0
  conceptsNovel : Nat := 0
  conceptsAliased : Nat := 0
  conceptsDegenerate : Nat := 0
  conceptsRefused : Nat := 0
  inventedEdges : Nat := 0

def Ledger.counts (l : Ledger) (agent : Name) : AgentCounts :=
  l.events.foldl (init := {}) fun c e =>
    if e.agent != agent then c else
    match e.kind with
    | .factAdmitted => { c with admitted := c.admitted + 1 }
    | .factRefuted => { c with refuted := c.refuted + 1 }
    | .factOpen => { c with opens := c.opens + 1 }
    | .factRepeat => c
    | .factDup => { c with dups := c.dups + 1 }
    | .refusedAtGate => { c with refused := c.refused + 1 }
    | .ruleBorn => { c with rulesBorn := c.rulesBorn + 1 }
    | .conceptAlias _ _ => { c with conceptsAliased := c.conceptsAliased + 1 }
    | .conceptDegenerate => { c with conceptsDegenerate := c.conceptsDegenerate + 1 }
    | .conceptNovel => { c with conceptsNovel := c.conceptsNovel + 1 }
    | .conceptRefused => { c with conceptsRefused := c.conceptsRefused + 1 }
    | .inventedEdge _ => { c with inventedEdges := c.inventedEdges + 1 }

def AgentCounts.describe (c : AgentCounts) : String :=
  s!"{c.admitted} admitted, {c.refuted} refuted, {c.dups} merged, \
{c.opens} open, {c.rulesBorn} birthed" ++
  (if c.conceptsNovel + c.conceptsAliased + c.conceptsDegenerate +
      c.conceptsRefused > 0 then
    s!", concepts: {c.conceptsNovel} novel/{c.conceptsAliased} aliased/\
{c.conceptsDegenerate} degenerate/{c.conceptsRefused} refused, \
{c.inventedEdges} vocabulary credits"
  else "")

end Runtime
end Eureka
