import Eureka

/-!
Deterministic concept-invention test: the lifecycle of DESIGN_INVENT, on a `Nat`
microcosm, exercising acceptance tests 2–6.

- **Refusals with reasons** (test 3): a non-`Prop` shape, a sorry-backed
  value, a metavariable-laden value, and a name clash — all refused at the
  birth gate, with reasons, never corpus residents.
- **Alias at birth**: `2 ∣ n` merges into `isEven` with a kernel-checked
  bridge (omega closes the expanded iff); a byte-identical rename merges
  by `rfl` — the pure-rename row of the verdict table.
- **Degenerate at birth** (test 5): the conjunction operator's
  `isEven ∧ isOdd` is provably empty — caught by the ⊥ probe, not left
  parading as novel.
- **A genuine novel survives** (test 2): `isEven ∧ isSmall` passes every
  probe, joins the pool, and earns certified specializes-edges.
- **Re-probe fires** (test 4): two concepts phrased through an opaque
  function are honestly un-alias-able at birth; a later corpus fact
  unlocks a certified edge between them, whose admission (a fact
  mentioning two invented predicates — trigger (i)) re-probes the pair
  and merges the younger into the elder. The budgeted sweep (trigger
  (ii)) runs before the unlock and correctly merges nothing.
- **The audit bites** (test 6): a def smuggled into the reserved
  namespace by raw `addDecl`, bypassing the gate, is flagged by
  `auditInvented` — the runtime counterpart of
  `defGated_concepts_invariant`.

Run with `lake env lean InventStub.lean`.
-/

open Lean Meta Eureka.Runtime

/-- The microcosm's canonical predicates — this domain's "library". -/
def isEven (n : Nat) : Prop := n % 2 = 0
def isOdd (n : Nat) : Prop := n % 2 = 1
def isSmall (n : Nat) : Prop := n < 10

/-- Opaque to the probes: not in the transparency set, no simp lemmas. -/
def opaqueDouble (n : Nat) : Nat := n + n

/-- Candidate bodies, written as ordinary defs and proposed from their
type/value pairs. -/
def cand_divisibleByTwo (n : Nat) : Prop := 2 ∣ n
def cand_evenAgain (n : Nat) : Prop := n % 2 = 0
def cand_notPred (n : Nat) : Nat := n
def cand_stuckA (n : Nat) : Prop := opaqueDouble n = 10
def cand_stuckB (n : Nat) : Prop := 2 * n = 10

/-- The enabling fact for the re-probe test — proved here so the stub can
admit it through the gate at the chosen moment. (A `def`, not a `theorem`:
theorem values elaborate asynchronously and are not readable from a
same-file `#eval`.) -/
def opaqueDouble_eq : ∀ n : Nat, opaqueDouble n = 2 * n :=
  fun n => (Nat.two_mul n).symm

def proposalFromDef (base : Name) (defn : Name) : MetaM ConceptProposal := do
  let ci ← getConstInfo defn
  return { name := base, type := ci.type, value := ci.value!, origin := base }

#eval show MetaM Unit from do
  let known ← collectKnown [`Nat]
  IO.println s!"grounding pool: {known.size} Nat.* library lemmas"
  let transparent := fun (n : Name) =>
    inventedNs.isPrefixOf n || [``isEven, ``isOdd, ``isSmall].contains n
  let ctx : ProbeCtx := { known, transparent }
  let mut canonical : Array ProbeTarget := #[]
  for n in [``isEven, ``isOdd, ``isSmall] do
    let some t ← probeTargetOfConst n | throwError "no probe target for {n}"
    canonical := canonical.push t
  -- The candidate batch: aliases, operator products, malformed shapes,
  -- and the stuck pair, interleaved.
  let mut proposals : Array ConceptProposal := #[]
  proposals := proposals.push (← proposalFromDef `divisibleByTwo ``cand_divisibleByTwo)
  proposals := proposals.push (← proposalFromDef `evenAgain ``cand_evenAgain)
  let some conjDegen ← mkConjProposal false canonical[0]! canonical[1]!
    | throwError "conjunction operator failed to build isEven ∧ isOdd"
  proposals := proposals.push conjDegen
  proposals := proposals.push (← proposalFromDef `notPred ``cand_notPred)
  let natToProp := Expr.forallE `n (mkConst ``Nat) (.sort .zero) .default
  proposals := proposals.push
    { name := `lazyPred, type := natToProp, value := ← mkSorry natToProp false }
  proposals := proposals.push
    { name := `vaguePred, type := natToProp, value := ← mkFreshExprMVar natToProp }
  let some conjNovel ← mkConjProposal false canonical[0]! canonical[2]!
    | throwError "conjunction operator failed to build isEven ∧ isSmall"
  proposals := proposals.push conjNovel
  proposals := proposals.push (← proposalFromDef `stuckA ``cand_stuckA)
  proposals := proposals.push (← proposalFromDef `stuckB ``cand_stuckB)
  -- Name clash: a second proposal under an already-admitted name.
  proposals := proposals.push (← proposalFromDef `divisibleByTwo ``cand_evenAgain)

  IO.println ""
  IO.println "── birth and identity probes ──"
  let (pool, corpus, stats) ← inventRound ctx {} {} canonical proposals
  IO.println s!"  {stats.describe}"
  unless stats.candidates == 10 do throwError "expected 10 candidates"
  unless stats.refused == 4 do
    throwError "expected 4 refusals (non-Prop, sorry, mvar, clash), got {stats.refused}"
  unless stats.degenerate == 1 do
    throwError "expected the ⊥ probe to catch isEven ∧ isOdd, got {stats.degenerate}"
  unless stats.aliased == 2 do
    throwError "expected 2 aliases at birth (2 ∣ n, the rename), got {stats.aliased}"
  unless stats.novel == 3 do
    throwError "expected 3 novel-so-far (the conj, stuckA, stuckB), got {stats.novel}"
  unless stats.edgeFacts ≥ 2 do
    throwError "expected the novel conjunction to earn specializes-edges"
  unless (pool.find? (inventedNs ++ `divisibleByTwo)).any
      (·.mergedInto == some ``isEven) do
    throwError "divisibleByTwo should be tombstoned into isEven"
  unless pool.isLive (inventedNs ++ `stuckA) && pool.isLive (inventedNs ++ `stuckB) do
    throwError "the stuck pair should both be live (unmergeable at birth)"

  IO.println ""
  IO.println "── sweep before the unlock (trigger ii): must merge nothing ──"
  let (pool, corpus, sweepMerges, cursor) ← sweepReprobe ctx pool corpus canonical 50 0
  unless sweepMerges.isEmpty do
    throwError "the sweep merged a pair that has no certificate yet"
  IO.println s!"  0 merges, cursor at {cursor} — honest silence"

  IO.println ""
  IO.println "── the unlock: a corpus fact, then the edge, then trigger (i) ──"
  let ci ← getConstInfo ``opaqueDouble_eq
  let some unlockFact ← commitFact
      { name := ← freshName `opaqueDouble_eq, stmt := ci.type, proof := ci.value! }
    | throwError "the gate refused the enabling fact"
  let corpus := { corpus with facts := corpus.facts.push unlockFact }
  IO.println s!"  ✓ {← ppExpr ci.type} — admitted as {unlockFact.name}"
  let stuckA := (pool.find? (inventedNs ++ `stuckA)).get!
  let stuckB := (pool.find? (inventedNs ++ `stuckB)).get!
  let some edgeStmt ← mkImplStmt stuckA.toTarget stuckB.toTarget
    | throwError "failed to build the edge statement"
  let some (edgePf, how) ← probeProve ctx corpus edgeStmt
    | throwError "the corpus fact should unlock the stuckA → stuckB edge"
  let some (corpus, edgeFact) ← commitProbeFact corpus "stuckA_imp_stuckB" edgeStmt edgePf
    | throwError "the gate refused the unlocked edge"
  IO.println s!"  ✓ {← ppExpr edgeStmt} — admitted ({how})"
  let (pool, corpus, merges) ← reprobeOnFact ctx pool corpus edgeFact
  unless merges == #[(inventedNs ++ `stuckB, inventedNs ++ `stuckA)] do
    throwError "trigger (i) should merge stuckB into stuckA, got {merges}"
  unless !pool.isLive (inventedNs ++ `stuckB) && pool.isLive (inventedNs ++ `stuckA) do
    throwError "expected stuckB tombstoned, stuckA alive"
  IO.println s!"  ≡ trigger (i) fired: stuckB merged into stuckA, bridge in corpus"

  IO.println ""
  IO.println "── the audit bites (adversarial round) ──"
  unless (← auditInvented pool).isEmpty do
    throwError "audit flagged a gate-admitted concept"
  let natTy := mkConst ``Nat
  let evilValue ← withLocalDeclD `n natTy fun n =>
    mkLambdaFVars #[n] (mkConst ``False)
  addDecl <| .defnDecl
    { name := inventedNs ++ `evil, levelParams := [], type := natToProp,
      value := evilValue, hints := .abbrev, safety := .safe }
  let violations ← auditInvented pool
  unless violations == #[inventedNs ++ `evil] do
    throwError "audit should flag exactly the smuggled def, got {violations}"
  IO.println s!"  ✗ {inventedNs ++ `evil} — flagged by the reserved-namespace audit"

  IO.println ""
  IO.println s!"corpus: {corpus.facts.size} kernel-certified facts \
(bridges, edges, the unlock); every admission gated"
  IO.println "concept lifecycle behaves as specified"
