import Eureka.Heuristics

/-!
# The symbolic mutation stream (DESIGN_CURATOR L4)

EURISKO's general move — mutation operators over heuristic source — with
the authoring kept out of untrusted hands. A mutable heuristic is a
*genome*: a list of law schemas over a list of operations. The mutation
operators (`substOp`, `restrictPool`, `crossover`) transform genomes
mechanically; the mutant enters the population as an ordinary `.rule`
birth — source emitted by `genomeSourceFor`, elaborated and
policy-checked by the rule gate, parent credit intact. Nobody authors:
the curator (or the round-robin baseline) only *chooses* target and
operator.

The emitted source is a single call to the trusted interpreter
`schemaPropose` with literal arguments, so a mutant's genome is fully
legible in its source and elaboration stays cheap. The genome vocabulary
is equation-schema-shaped by construction: the tautology-farm exploit
(`∨ True`, refl) is not in its generative space.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- The law schemas the mutator can instantiate. Single-op schemas fire
per operation; pair schemas fire per ordered pair of distinct
operations. -/
inductive SchemaTag where
  | comm      -- op a b = op b a
  | assoc     -- op (op a b) c = op a (op b c)
  | idem      -- op a a = a
  | absorb    -- op1 a (op2 a b) = a                (pair)
  | distribL  -- op1 a (op2 b c) = op2 (op1 a b) (op1 a c)   (pair)
  deriving BEq, Repr, Inhabited

def SchemaTag.tag : SchemaTag → String
  | .comm => "comm" | .assoc => "assoc" | .idem => "idem"
  | .absorb => "absorb" | .distribL => "distribL"

def SchemaTag.isPair : SchemaTag → Bool
  | .absorb | .distribL => true
  | _ => false

/-- A mutable heuristic's genome: which law schemas, over which
operations. The mutation operators act here; the source is derived. -/
structure MutGenome where
  schemas : List SchemaTag
  ops : List Op
  deriving Inhabited

/-- Deterministic mutant name, doubling as dedup key: same genome, same
name, and the loop's already-born skip does the rest. -/
def MutGenome.mutName (g : MutGenome) : Name :=
  .mkSimple <| "mut_" ++ String.intercalate "_" (g.schemas.map (·.tag))
    ++ "__" ++ String.intercalate "_" (g.ops.map (·.tag))

private def natTy : Expr := mkConst ``Nat

/-- The trusted genome interpreter: instantiate every schema over the
genome's operations. Referenced by emitted mutant source; untrusted code
never builds these `Expr`s itself. -/
def schemaPropose (origin : Name) (schemas : List SchemaTag)
    (ops : List Op) : Corpus → MetaM (Array Conjecture) := fun _ => do
  let mut out : Array Conjecture := #[]
  for s in schemas do
    if s.isPair then
      for op1 in ops do
        for op2 in ops do
          unless op1.head == op2.head do
            let nm := .mkSimple s!"{origin}_{s.tag}_{op1.tag}_{op2.tag}"
            let stmt ← match s with
              | .absorb =>
                withLocalDeclD `a natTy fun a =>
                  withLocalDeclD `b natTy fun b => do
                    mkForallFVars #[a, b]
                      (← mkEq (← mkOp op1 a (← mkOp op2 a b)) a)
              | _ =>
                withLocalDeclD `a natTy fun a =>
                  withLocalDeclD `b natTy fun b =>
                    withLocalDeclD `c natTy fun c => do
                      let lhs ← mkOp op1 a (← mkOp op2 b c)
                      let rhs ← mkOp op2 (← mkOp op1 a b) (← mkOp op1 a c)
                      mkForallFVars #[a, b, c] (← mkEq lhs rhs)
            out := out.push ⟨nm, stmt, origin⟩
    else
      for op in ops do
        let nm := .mkSimple s!"{origin}_{s.tag}_{op.tag}"
        let stmt ← match s with
          | .comm =>
            withLocalDeclD `a natTy fun a =>
              withLocalDeclD `b natTy fun b => do
                mkForallFVars #[a, b]
                  (← mkEq (← mkOp op a b) (← mkOp op b a))
          | .assoc =>
            withLocalDeclD `a natTy fun a =>
              withLocalDeclD `b natTy fun b =>
                withLocalDeclD `c natTy fun c => do
                  let lhs ← mkOp op (← mkOp op a b) c
                  let rhs ← mkOp op a (← mkOp op b c)
                  mkForallFVars #[a, b, c] (← mkEq lhs rhs)
          | _ =>
            withLocalDeclD `a natTy fun a => do
              mkForallFVars #[a] (← mkEq (← mkOp op a a) a)
        out := out.push ⟨nm, stmt, origin⟩
  return out

private def schemaLit (s : SchemaTag) : String := s!".{s.tag}"

private def opLit (op : Op) : String := s!"⟨\"{op.tag}\", ``{op.head}⟩"

/-- Emit a mutant's source: one call to the trusted interpreter with
literal arguments. Elaborated, policy-checked, and compiled by the rule
gate like any born code. -/
def genomeSourceFor (g : MutGenome) : String :=
  let name := g.mutName
  let schemas := String.intercalate ", " (g.schemas.map schemaLit)
  let ops := String.intercalate ", " (g.ops.map opLit)
  s!"fun corpus => schemaPropose `{name} [{schemas}] [{ops}] corpus"

/-- The mutation operators. `crossover` names a donor genome. -/
inductive MutOp where
  | substOp
  | restrictPool
  | crossover (donor : Name)
  deriving BEq, Repr, Inhabited

/-- `substOp`: replace the cursor-selected operation with the first pool
operation absent from the genome. `none` when the genome already spans
the pool. -/
def applySubstOp (g : MutGenome) (cursor : Nat) : Option MutGenome := do
  let fresh ← opPool.find? fun op => !g.ops.any (·.head == op.head)
  if g.ops.isEmpty then none else
  let k := cursor % g.ops.length
  some { g with ops := g.ops.mapIdx fun i op =>
    if i == k then fresh else op }

/-- `restrictPool`: drop the last operation. `none` below two
operations. (The earned-aware version — keep only operations whose facts
admitted — wants the ledger; ruled a refinement, not slice one.) -/
def applyRestrictPool (g : MutGenome) : Option MutGenome :=
  if g.ops.length ≥ 2 then some { g with ops := g.ops.dropLast } else none

/-- `crossover`: this genome's schemas over the donor's operations. -/
def applyCrossover (g donor : MutGenome) : Option MutGenome :=
  let g' : MutGenome := { schemas := g.schemas, ops := donor.ops }
  if g'.mutName == g.mutName || g'.mutName == donor.mutName then none
  else some g'

def applyMutOp (g : MutGenome) (op : MutOp) (cursor : Nat)
    (donor : Option MutGenome) : Option MutGenome :=
  match op with
  | .substOp => applySubstOp g cursor
  | .restrictPool => applyRestrictPool g
  | .crossover _ => donor.bind (applyCrossover g)

/-- Genomes for the hand-written template heuristics, so the mutation
stream can start from them (`DESIGN_CURATOR` test 3: `mutate comm
substOp` births the swapped family). -/
def templateGenomes : List (Name × MutGenome) :=
  [(`comm, ⟨[.comm], opPool⟩),
   (`assoc, ⟨[.assoc], opPool⟩),
   (`idem, ⟨[.idem], opPool⟩),
   (`distrib, ⟨[.distribL], opPool⟩)]

end Runtime
end Eureka
