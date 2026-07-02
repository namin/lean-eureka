import Eureka.Runtime

/-!
# Generative heuristics

Heuristics that *derive* conjectures rather than recite them: algebraic-law
templates instantiated over a pool of operations (the LeanDisco pattern),
plus a corpus-reading heuristic (`mixerH`) whose proposals only exist once
earlier discoveries are in the corpus — the generational move.

Everything here is untrusted. A heuristic's output is a `Conjecture`:
a statement with no evidence attached.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- A conjecture: a statement without evidence, and the heuristic that
proposed it. -/
structure Conjecture where
  name : Name
  stmt : Expr
  origin : Name

/-- A heuristic that proposes conjectures from the corpus. -/
structure ConjHeuristic where
  name : Name
  propose : Corpus → MetaM (Array Conjecture)

/-- A binary operation on `Nat`, named by the surface constant the library
states its lemmas with, so grounding certificates match syntactically. -/
structure Op where
  tag : String
  head : Name

def opPool : List Op :=
  [⟨"add", ``HAdd.hAdd⟩, ⟨"mul", ``HMul.hMul⟩, ⟨"sub", ``HSub.hSub⟩,
   ⟨"pow", ``HPow.hPow⟩, ⟨"max", ``Max.max⟩, ⟨"min", ``Min.min⟩,
   ⟨"gcd", ``Nat.gcd⟩]

def mkOp (op : Op) (a b : Expr) : MetaM Expr :=
  mkAppM op.head #[a, b]

private def natTy : Expr := mkConst ``Nat

/-- `∀ n, op n c = n` and `∀ n, op c n = n` for small constants `c`:
identity-element candidates. -/
def identityH : ConjHeuristic where
  name := `identity
  propose _ := do
    let mut out := #[]
    for op in opPool do
      for c in [0, 1] do
        let cLit := mkNatLit c
        let right ← withLocalDeclD `n natTy fun n => do
          mkForallFVars #[n] (← mkEq (← mkOp op n cLit) n)
        let left ← withLocalDeclD `n natTy fun n => do
          mkForallFVars #[n] (← mkEq (← mkOp op cLit n) n)
        out := out.push ⟨.mkSimple s!"{op.tag}_rid_{c}", right, `identity⟩
        out := out.push ⟨.mkSimple s!"{op.tag}_lid_{c}", left, `identity⟩
    return out

/-- `∀ a b, op a b = op b a`. -/
def commH : ConjHeuristic where
  name := `comm
  propose _ := do
    let mut out := #[]
    for op in opPool do
      let stmt ← withLocalDeclD `a natTy fun a =>
        withLocalDeclD `b natTy fun b => do
          mkForallFVars #[a, b] (← mkEq (← mkOp op a b) (← mkOp op b a))
      out := out.push ⟨.mkSimple s!"{op.tag}_comm", stmt, `comm⟩
    return out

/-- `∀ a, op a a = a`. -/
def idemH : ConjHeuristic where
  name := `idem
  propose _ := do
    let mut out := #[]
    for op in opPool do
      let stmt ← withLocalDeclD `a natTy fun a => do
        mkForallFVars #[a] (← mkEq (← mkOp op a a) a)
      out := out.push ⟨.mkSimple s!"{op.tag}_idem", stmt, `idem⟩
    return out

/-- `∀ a b c, op (op a b) c = op a (op b c)`. -/
def assocH : ConjHeuristic where
  name := `assoc
  propose _ := do
    let mut out := #[]
    for op in opPool do
      let stmt ← withLocalDeclD `a natTy fun a =>
        withLocalDeclD `b natTy fun b =>
          withLocalDeclD `c natTy fun c => do
            mkForallFVars #[a, b, c]
              (← mkEq (← mkOp op (← mkOp op a b) c) (← mkOp op a (← mkOp op b c)))
      out := out.push ⟨.mkSimple s!"{op.tag}_assoc", stmt, `assoc⟩
    return out

/-- `∀ a b c, op₁ a (op₂ b c) = op₂ (op₁ a b) (op₁ a c)`: distributivity
candidates over ordered pairs of distinct operations. -/
def distribH : ConjHeuristic where
  name := `distrib
  propose _ := do
    let pool := opPool.filter (·.tag ∈ ["add", "mul", "max", "min", "gcd"])
    let mut out := #[]
    for op1 in pool do
      for op2 in pool do
        unless op1.head == op2.head do
          let stmt ← withLocalDeclD `a natTy fun a =>
            withLocalDeclD `b natTy fun b =>
              withLocalDeclD `c natTy fun c => do
                mkForallFVars #[a, b, c]
                  (← mkEq (← mkOp op1 a (← mkOp op2 b c))
                          (← mkOp op2 (← mkOp op1 a b) (← mkOp op1 a c)))
          out := out.push ⟨.mkSimple s!"{op1.tag}_distrib_{op2.tag}", stmt, `distrib⟩
    return out

/-- Recognize admitted right-identity facts `∀ n, op n c = n` in the corpus. -/
def rightIdentities (corpus : Corpus) : MetaM (Array (Op × Expr)) := do
  let mut out := #[]
  for f in corpus.facts do
    let hit ← forallTelescope f.stmt fun xs body => do
      if h : xs.size = 1 then
        let x := xs[0]
        match body.eq? with
        | some (_, lhs, rhs) =>
          if rhs == x then
            let args := lhs.getAppArgs
            if args.size ≥ 2 then
              let a := args[args.size - 2]!
              let c := args[args.size - 1]!
              if a == x && !c.hasFVar then
                match opPool.find? (fun op => lhs.getAppFn.constName? == some op.head) with
                | some op => return some (op, c)
                | none => return none
          return none
        | none => return none
      else return none
    if let some pair := hit then
      out := out.push pair
  return out

/-- The corpus reader: for admitted right identities `(op₁, c₁)` and
`(op₂, c₂)`, conjecture `∀ a, op₁ (op₂ a c₂) c₁ = a`. These conjectures
cannot be proposed before the identities are discovered — second-generation
discovery by construction. -/
def mixerH : ConjHeuristic where
  name := `mixer
  propose corpus := do
    let ids ← rightIdentities corpus
    let mut out := #[]
    for (op1, c1) in ids do
      for (op2, c2) in ids do
        unless op1.head == op2.head do
          let stmt ← withLocalDeclD `a natTy fun a => do
            mkForallFVars #[a] (← mkEq (← mkOp op1 (← mkOp op2 a c2) c1) a)
          out := out.push ⟨.mkSimple s!"mix_{op2.tag}_{op1.tag}", stmt, `mixer⟩
    return out

end Runtime
end Eureka
