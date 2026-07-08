import Eureka.Mutate

/-!
# The curator: action grammar and prompt (DESIGN_CURATOR L1, L8)

The LLM in Lenat's seat. Its reply is parsed against a closed action
menu — boost, damp, flag, escalate, mutate, label — one action per
line, strictly; anything else drops and is logged. Every action is
schedule-only by type: none constructs a statement, a heuristic, a
concept, or a price. The adversarial worst case is wasted attention,
which the economy prices (W4: `discovery_sound` quantifies over
adversarial schedules).
-/

open Lean

namespace Eureka
namespace Runtime

/-- The closed action menu (L1). -/
inductive CuratorAction where
  | boost (agent : Name)
  | damp (agent : Name)
  /-- Flag an admitted fact as trivial-in-spirit: cancels its admission
  pay to its origin agent (L6). One flag per fact, loop-enforced. -/
  | flag (fact : Name)
  /-- Nominate an open conjecture for the escalation pass (L5). -/
  | escalate (conj : Name)
  /-- Apply a symbolic mutation operator to a genome-backed agent (L4).
  The curator chooses; the mechanical mutator writes. -/
  | mutate (target : Name) (op : MutOp)
  /-- Display-layer only: a human-legible label or note. -/
  | label (target : Name) (text : String)
  deriving Repr, Inhabited

/-- Strict line parser: `(actions, dropped)`. Unknown verbs, wrong
arities, and prose land in `dropped` — logged, never acted on. -/
def parseCuratorReply (text : String) : Array CuratorAction × Array String :=
  Id.run do
    let mut actions : Array CuratorAction := #[]
    let mut dropped : Array String := #[]
    for lineSlice in text.split (· == '\n') do
      let line := lineSlice.toString.trimAscii.toString
      if line.isEmpty then continue
      let toks := (line.splitOn " ").filter (!·.isEmpty)
      let act? : Option CuratorAction := match toks with
        | ["boost", a] => some (.boost a.toName)
        | ["damp", a] => some (.damp a.toName)
        | ["flag", f] => some (.flag f.toName)
        | ["escalate", c] => some (.escalate c.toName)
        | ["mutate", t, "substOp"] => some (.mutate t.toName .substOp)
        | ["mutate", t, "restrictPool"] => some (.mutate t.toName .restrictPool)
        | ["mutate", t, "crossover", d] =>
          some (.mutate t.toName (.crossover d.toName))
        | "label" :: t :: rest =>
          if rest.isEmpty then none
          else some (.label t.toName (String.intercalate " " rest))
        | _ => none
      match act? with
      | some a => actions := actions.push a
      | none => dropped := dropped.push line
    return (actions, dropped)

/-- The curate-pass prompt (L8): agenda with worths, the generation's
outcomes, the mutable genomes, and the grammar — nothing else. The
curator sees the run; it never sees a channel to write into it. -/
def renderCuratorPrompt (generation : Nat) (agenda : String)
    (outcomes : String) (mutables : String) : String :=
  s!"You are the CURATOR of a verified mathematical discovery system — \
the Lenat seat. A symbolic engine proposes conjectures and mutations; a \
kernel gate alone decides truth. You steer only ATTENTION: which agents \
get budget, which admitted facts were trivial, which open conjectures \
deserve deeper proof search, which heuristics to mutate. You cannot \
author statements or heuristics, and nothing you do can admit a fact.

Generation {generation} agenda (agent worth-per-attention):
{agenda}
This generation's outcomes:
{outcomes}
Mutable heuristics (genome-backed; mutation operators: substOp, \
restrictPool, crossover <donor>):
{mutables}
Reply with one action per line, from EXACTLY this menu (no prose, no
markdown, at most 8 lines):
boost <agent>
damp <agent>
flag <fact-name>
escalate <conjecture-name>
mutate <agent> substOp
mutate <agent> restrictPool
mutate <agent> crossover <agent>
label <name> <free text note>

Guidance: damp agents producing refuted or trivial output; flag admitted \
facts that are tautological or content-free (their pay is cancelled); \
boost agents opening genuinely new territory; mutate heuristics whose \
family is exhausted toward operations that are earning."

end Runtime
end Eureka
