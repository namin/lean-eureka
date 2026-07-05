import Eureka

/-!
Deterministic concept-booth test: the DESIGN_INVENT D6 pipeline with a
canned transport standing in for the LLM. Two rounds on the `Nat`
microcosm:

- Round 1 mixes prose (dropped), an unparseable body, an unknown shape
  tag, an alias in disguise (`2 ∣ n`, merged into `isEven` at birth), a
  degenerate (`n < n`, certified empty), and a genuine novel that joins
  the pool and earns edges.
- Round 2 re-proposes the novel under its own name (refused: name clash —
  visible in the feedback), and lands a second novel.

The booth's log — merged/degenerate/novel/refused/unparseable — is what
a live model sees as feedback; the stub asserts the pipeline's counts.
Run with `lake env lean InventBoothStub.lean`.
-/

open Lean Meta Eureka.Runtime

def isEven (n : Nat) : Prop := n % 2 = 0
def isOdd (n : Nat) : Prop := n % 2 = 1
def isSmall (n : Nat) : Prop := n < 10

def round1 : String :=
"Here are my proposals:
bigEven | nat | n % 2 = 0 ∧ 10 < n
evenish | nat | 2 ∣ n
impossible | nat | n < n
broken | nat | n +
weird | matrix | n = n"

def round2 : String :=
"bigEven | nat | n % 2 = 0 ∧ 10 < n
tiny | nat | n < 3"

/-- The canned transport: round texts in order, then errors. -/
def cannedCall (texts : Array String) (counter : IO.Ref Nat) :
    String → IO (Except String String) := fun _ => do
  let i ← counter.get
  counter.set (i + 1)
  if h : i < texts.size then return .ok texts[i]
  else return .error "out of canned rounds"

#eval show MetaM Unit from do
  let known ← collectKnown [`Nat]
  let transparent := fun (n : Name) =>
    inventedNs.isPrefixOf n || [``isEven, ``isOdd, ``isSmall].contains n
  let ctx : ProbeCtx := { known, transparent }
  let mut canonical : Array ProbeTarget := #[]
  for n in [``isEven, ``isOdd, ``isSmall] do
    let some t ← probeTargetOfConst n | throwError "no probe target for {n}"
    canonical := canonical.push t
  let natToProp := Expr.forallE `n (mkConst ``Nat) (.sort .zero) .default
  let shapes : Array ConceptShape := #[⟨"nat", "(n : Nat)", natToProp⟩]
  let counter ← IO.mkRef 0
  let (pool, corpus, stats) ← conceptBooth
    (cannedCall #[round1, round2] counter) ctx canonical
    { rounds := 2, perRound := 4, shapes
      render := renderConceptPrompt "unary predicates on Nat" shapes }
  IO.println ""
  IO.println s!"  {stats.describe}"
  -- Round 1: bigEven novel, evenish ≡ isEven, impossible degenerate,
  -- broken + weird unparseable. Round 2: bigEven name clash, tiny novel.
  unless stats.candidates == 5 do
    throwError "expected 5 parsed candidates across rounds, got {stats.candidates}"
  unless stats.aliased == 1 do
    throwError "expected evenish merged into isEven, got {stats.aliased}"
  unless stats.degenerate == 1 do
    throwError "expected impossible certified degenerate, got {stats.degenerate}"
  unless stats.refused == 1 do
    throwError "expected the round-2 name clash refusal, got {stats.refused}"
  unless stats.novel == 2 do
    throwError "expected bigEven and tiny as the novels, got {stats.novel}"
  unless (pool.find? (inventedNs ++ `evenish)).any (·.mergedInto == some ``isEven) do
    throwError "evenish should be tombstoned into isEven"
  unless pool.isLive (inventedNs ++ `bigEven) && pool.isLive (inventedNs ++ `tiny) do
    throwError "the novels should be live"
  unless (← auditInvented pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  IO.println s!"corpus: {corpus.facts.size} kernel-certified facts"
  IO.println "concept booth behaves as specified"
