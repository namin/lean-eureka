import Eureka.Prover
import Eureka.Heuristics

/-!
# The discovery loop

Generations of: heuristics propose (reading the corpus), the counterexample
search refutes, the prover ladder supports, and the gate — alone — admits.
Fixpoint when a generation proposes nothing new.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- A fresh, `disco.`-prefixed declaration name. -/
def freshName (base : Name) : MetaM Name := do
  let env ← getEnv
  let base := `disco ++ base
  if !env.contains base then return base
  let mut i := 1
  while env.contains (base.appendIndexAfter i) do
    i := i + 1
  return base.appendIndexAfter i

structure DiscoStats where
  admitted : Nat := 0
  refuted : Nat := 0
  «open» : Nat := 0
  refused : Nat := 0
  merged : Nat := 0

/-- The fate of one deduplicated conjecture. -/
inductive Outcome where
  | admitted (f : Fact) (note : String)
  | refuted (cex : String)
  | stillOpen
  | refusedAtGate

/-- A domain refuter: given a conjecture statement, optionally return a
kernel-checkable refutation — the negated instance, its proof, and a
description of the witness. `refuteByInstances` (domain layer) produces
these; the default refuter is silent, and silence never certifies truth. -/
abbrev Refuter := Expr → MetaM (Option (Expr × Expr × String))

/-- The per-judgment heartbeat budget: the default command budget, pinned.
Long-running drivers may raise the *command* ceiling (`set_option
maxHeartbeats`) for loop overhead — reply parsing, dedup scans, printing —
without silently deepening the prover: a rung that times out in CI times
out identically in every driver. -/
def judgeHeartbeats : Nat := 200000

/-- Judge one conjecture: refute if the domain can, else hunt for evidence
and, on support, admit through the gate. A refutation is itself a fact —
the negated instance — and enters the corpus through `commitFact` like any
other: false conjectures die by the same evidence standard by which true
ones live. The corpus grows on `admitted` and on certified refutation. One
conjecture, one heartbeat budget (`judgeHeartbeats`) — a long run's earlier
judgments must not starve later ones, and a raised command ceiling must not
feed them. -/
def judge (known : Array KnownLemma) (corpus : Corpus) (c : Conjecture)
    (refuter : Refuter := fun _ => pure none) :
    MetaM (Corpus × Outcome) :=
  withOptions (fun o => o.set `maxHeartbeats judgeHeartbeats) <|
    withCurrHeartbeats do
  if let some (negStmt, pf, witness) ← refuter c.stmt then
    let nm ← freshName (c.name.appendAfter "_refuted")
    match ← commitFact { name := nm, stmt := negStmt, proof := pf } with
    | some f =>
      return ({ corpus with facts := corpus.facts.push f }, .refuted witness)
    | none =>
      -- the alleged refutation failed the gate: fall through to the hunt
      pure ()
  match ← hunt known (corpus.facts.map (·.name)) c.stmt with
  | .refuted cex => return (corpus, .refuted cex)
  | .stillOpen => return (corpus, .stillOpen)
  | .proved pf rung knownAs =>
    let nm ← freshName c.name
    match ← commitFact { name := nm, stmt := c.stmt, proof := pf } with
    | some f =>
      let note := match knownAs with
        | some k => s!"grounded: {k}"
        | none => rung
      return ({ corpus with facts := corpus.facts.push f }, .admitted f note)
    | none => return (corpus, .refusedAtGate)

/-- Run the loop. Every fact in the returned corpus went through
`commitFact`: screened, kernel-checked, axiom-audited. -/
def discover (heuristics : List ConjHeuristic) (generations : Nat := 3) :
    MetaM Corpus := do
  let known ← collectKnown [`Nat]
  IO.println s!"grounding pool: {known.size} Nat.* library lemmas"
  let mut corpus : Corpus := {}
  let mut attempted : Array (Expr × Name) := #[]
  let mut stats : DiscoStats := {}
  for gen in [1 : generations + 1] do
    IO.println ""
    IO.println s!"── generation {gen} ──"
    let mut fresh : Array Conjecture := #[]
    for h in heuristics do
      let cs ← try h.propose corpus catch _ => pure #[]
      for c in cs do
        -- Verbatim re-proposal (heuristics re-fire every generation): skip.
        if attempted.any (fun p => p.1 == c.stmt) then
          continue
        -- New statement, but definitionally an already-attempted one: a
        -- genuine alias — the synonym tower, caught and logged at proposal
        -- time.
        let mut alias? : Option Name := none
        for (a, nm) in attempted do
          if ← defeqSafe a c.stmt then
            alias? := some nm
            break
        match alias? with
        | some nm =>
          stats := { stats with merged := stats.merged + 1 }
          attempted := attempted.push (c.stmt, nm)
          IO.println s!"  ≡ [{c.origin}] {toString (← ppExpr c.stmt)} — \
definitionally identical to {nm}, merged"
        | none =>
          attempted := attempted.push (c.stmt, c.name)
          fresh := fresh.push c
    if fresh.isEmpty then
      IO.println "no new conjectures — fixpoint."
      break
    for c in fresh do
      let pretty := toString (← ppExpr c.stmt)
      let (corpus', outcome) ← judge known corpus c
      corpus := corpus'
      match outcome with
      | .refuted cex =>
        stats := { stats with refuted := stats.refuted + 1 }
        IO.println s!"  ✗ [{c.origin}] {pretty} — refuted ({cex})"
      | .stillOpen =>
        stats := { stats with «open» := stats.open + 1 }
        IO.println s!"  ? [{c.origin}] {pretty} — open"
      | .admitted _ note =>
        stats := { stats with admitted := stats.admitted + 1 }
        IO.println s!"  ✓ [{c.origin}] {pretty} — admitted ({note})"
      | .refusedAtGate =>
        stats := { stats with refused := stats.refused + 1 }
        IO.println s!"  ! [{c.origin}] {pretty} — prover evidence REFUSED by the gate"
  IO.println ""
  IO.println s!"{stats.admitted} admitted (every one kernel-gated), \
{stats.refuted} refuted, {stats.open} open, {stats.merged} merged as \
definitional duplicates, {stats.refused} refused at the gate"
  return corpus

end Runtime
end Eureka
