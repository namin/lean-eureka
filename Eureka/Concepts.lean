import Eureka.Loop

/-!
# Concept invention: definitions as a gated proposal kind

The lifecycle from DESIGN_INVENT: a candidate definition is **screened** (shape,
no sorry/mvars, `Prop`-valued), **born** by `addDecl` into the reserved
`Invented` namespace — the kernel checks the definition exactly as
`commitFact`'s kernel step checks a proof — then **probed** for identity
against a pool of canonical predicates and earlier inventions, and only
then lives in the pool, where identity remains a standing obligation
(re-probe triggers, budgeted sweep).

Verdicts are certificates (DESIGN_INVENT D4): an *alias* is a kernel-checked
`C ↔ C'` bridge admitted through the ordinary fact gate; *specializes* /
*generalizes* are certified implication edges; *degenerate* is an alias
to ⊤/⊥ (a certified `∀ xs, C xs` or `∀ xs, ¬ C xs`); *novel-so-far* names
the non-monotonicity honestly — the probe's power grows with the corpus.

A **merge** is tombstone + bridge, never a rewrite: the certified iff
enters the corpus as a fact, the merged concept stops proposing, and its
facts stay legible through the bridge. The merge *is* a discovery.

Everything on the hunt side is untrusted, as always: nothing reaches the
corpus except through `commitFact`, and nothing reaches the concept pool
except through `commitConcept` — screen, kernel, axiom audit. The
reserved-namespace audit (`auditInvented`) is the runtime counterpart of
the model's `defGated_concepts_invariant`.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- The reserved namespace for invented definitions. The birth gate places
concepts here; `auditInvented` checks nothing else lives here. -/
def inventedNs : Name := `Invented

/-- A proposal for a new concept, from an untrusted proposer: a base name
(the gate prefixes the reserved namespace), a type, and a value. Slice one
admits `Prop`-valued predicates only — the shapes the probes can touch. -/
structure ConceptProposal where
  name : Name
  type : Expr
  value : Expr
  origin : Name := `anonymous
  /-- Generative depth (DESIGN_INVENT C2): 1 for products of canonical
  inputs and direct proposals; compounding an invented input adds one. -/
  depth : Nat := 1

/-- A concept the gate has admitted: an invented definition living in the
reserved namespace. `mergedInto` is the tombstone — a merged concept stays
in the pool (its facts remain legible through the bridge) but stops
proposing and stops being a probe target. -/
structure Concept where
  name : Name
  type : Expr
  value : Expr
  origin : Name := `anonymous
  depth : Nat := 1
  mergedInto : Option Name := none
  deriving Inhabited

/-- The concept pool: birth-ordered, tombstones included. -/
structure ConceptPool where
  concepts : Array Concept := #[]
  deriving Inhabited

/-- Concepts that are alive: born and not merged away. -/
def ConceptPool.live (pool : ConceptPool) : Array Concept :=
  pool.concepts.filter (·.mergedInto.isNone)

def ConceptPool.find? (pool : ConceptPool) (n : Name) : Option Concept :=
  pool.concepts.find? (·.name == n)

def ConceptPool.isLive (pool : ConceptPool) (n : Name) : Bool :=
  (pool.find? n).any (·.mergedInto.isNone)

/-- Tombstone `n` as merged into `into`. -/
def ConceptPool.merge (pool : ConceptPool) (n into : Name) : ConceptPool :=
  { pool with concepts := pool.concepts.map fun c =>
      if c.name == n then { c with mergedInto := some into } else c }

/-- The cheap front of the birth gate: refusals carry reasons (the
baseline's 54% malformed-candidate rate should be visible refusals, not
corpus residents). Slice one requires a `Prop`-valued predicate — a
telescope ending in `Prop` — because every probe rung works by applying
the concept and reasoning about the resulting proposition. The def is
built by the gate itself (`commitConcept`), so `partial`/`unsafe`
declarations, instances, and attributes are unrepresentable rather than
screened. -/
def screenConcept (p : ConceptProposal) : MetaM (Except String Unit) := do
  if p.type.hasSorry || p.value.hasSorry then
    return .error "contains sorry"
  if p.type.hasMVar || p.value.hasMVar then
    return .error "contains metavariables"
  if p.type.hasFVar || p.value.hasFVar then
    return .error "contains free variables"
  if p.type.hasLevelMVar || p.value.hasLevelMVar then
    return .error "contains universe metavariables"
  let isPred ← (do
    let r ← attempt <| forallTelescope p.type fun _ body =>
      return body == .sort .zero
    pure (r.getD false))
  unless isPred do
    return .error "not a Prop-valued predicate"
  let tyOk ← (do
    let r ← attempt do
      let vty ← inferType p.value
      withNewMCtxDepth (isDefEq vty p.type)
    pure (r.getD false))
  unless tyOk do
    return .error "value does not have the declared type"
  return .ok ()

/-- The birth gate: screen, declare into the reserved namespace — the
kernel checks the definition, exactly parallel to `commitFact` — then
audit the axioms the definition's body depends on. On any refusal the
gate's own additions are rolled back; refusal is safe. The runtime
instance of the model's `admitDefGated`. -/
def commitConcept (pool : ConceptPool) (p : ConceptProposal) :
    MetaM (Except String (ConceptPool × Concept)) := withCurrHeartbeats do
  if let .error r ← screenConcept p then
    return .error r
  let name := inventedNs ++ p.name
  if (← getEnv).contains name then
    return .error s!"name clash: {name} already declared"
  let env ← getEnv
  try
    addDecl <| .defnDecl
      { name, levelParams := [], type := p.type, value := p.value,
        hints := .abbrev, safety := .safe }
  catch _ =>
    setEnv env
    return .error "kernel refused the definition"
  let axioms ← try collectAxioms name catch _ => setEnv env; return .error "axiom audit failed"
  unless axioms.all allowedAxioms.contains do
    setEnv env
    return .error "definition depends on disallowed axioms"
  let c : Concept :=
    { name, type := p.type, value := p.value, origin := p.origin,
      depth := p.depth }
  return .ok ({ pool with concepts := pool.concepts.push c }, c)

/-- The reserved-namespace audit: every constant under `Invented` must
descend from a gate-admitted concept (the concept itself, or elaborator
auxiliaries the concept's name prefixes — equation lemmas and the like).
Returns the violations. This is the runtime counterpart of the model's
`defGated_concepts_invariant`: heuristics have raw `addDecl` power, so
the boundary is audited, not assumed. -/
def auditInvented (pool : ConceptPool) : MetaM (Array Name) := do
  let env ← getEnv
  let residents : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if inventedNs.isPrefixOf n && n != inventedNs then acc.push n else acc
  return residents.filter fun n =>
    !pool.concepts.any fun c => c.name == n || c.name.isPrefixOf n

/-!
## Probe targets and statement builders

A probe target is anything the newborn can be compared against: a
canonical predicate from the ambient library, or an earlier invention.
Statements come in a *folded* form (the constants themselves — what gets
committed, keeping certificates legible) and an *expanded* form
(delta-expanded through a caller-chosen transparency set — what the
arithmetic and propositional rungs can actually see). A proof of the
expanded form is a proof of the folded form: they are definitionally
equal, and both the screen and the kernel check up to defeq.
-/

/-- A probe target: name, type and universe levels (instantiated), and the
definition body when there is one. -/
structure ProbeTarget where
  name : Name
  type : Expr
  levels : List Level := []
  deriving Inhabited

def Concept.toTarget (c : Concept) : ProbeTarget :=
  { name := c.name, type := c.type }

/-- A target from an environment constant. Constants with one universe
parameter are admitted instantiated at `Level.zero` (the `collectKnown`
convention); more are skipped. -/
def probeTargetOfConst (n : Name) : MetaM (Option ProbeTarget) := do
  let some ci := (← getEnv).find? n | return none
  match ci.levelParams with
  | [] => return some { name := n, type := ci.type }
  | [u] =>
    return some { name := n, type := ci.type.instantiateLevelParams [u] [.zero],
                  levels := [.zero] }
  | _ => return none

/-- Two targets are comparable when their types agree definitionally. The
cheap prefilter before any probe is spent. -/
def targetsCompatible (a b : ProbeTarget) : MetaM Bool :=
  defeqSafe a.type b.type

/-- Delta-expand the constants selected by `transparent` (recursively, with
beta), leaving everything else folded. The probe's expanded forms come from
here: `fun n => inventedNs.isPrefixOf n` unfolds invented vocabulary one
honest level; domains may widen the set. -/
partial def expandConsts (transparent : Name → Bool) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun node => do
    -- Rewrite at *application* nodes only: post-order visits the bare
    -- const first, and rewriting there would leave the enclosing
    -- application headed by a lambda — a beta-redex that defeats every
    -- head-indexed rung (compose, known, chain) downstream.
    if node.isApp then
      if let .const n ls := node.getAppFn then
        if transparent n then
          if let some ci := (← getEnv).find? n then
            if let some v := ci.value? then
              let v := v.instantiateLevelParams ci.levelParams ls
              return .visit (mkAppN v node.getAppArgs).headBeta
      -- Collapse redexes created by inner rewrites (post-order builds
      -- applications up around already-substituted heads).
      if node.getAppFn.isLambda then
        return .visit node.headBeta
    return .continue node)

private def targetApp (t : ProbeTarget) (xs : Array Expr) : Expr :=
  mkAppN (mkConst t.name t.levels) xs

/-- `∀ xs, C xs ↔ T xs`, folded. -/
def mkIffStmt (c t : ProbeTarget) : MetaM (Option Expr) := do
  let r ← attempt <| forallTelescope c.type fun xs body => do
    unless body == .sort .zero do return none
    return some (← mkForallFVars xs
      (mkApp2 (mkConst ``Iff) (targetApp c xs) (targetApp t xs)))
  return r.join

/-- `∀ xs, C xs → T xs`, folded. -/
def mkImplStmt (c t : ProbeTarget) : MetaM (Option Expr) := do
  let r ← attempt <| forallTelescope c.type fun xs body => do
    unless body == .sort .zero do return none
    return some (← mkForallFVars xs
      (← mkArrow (targetApp c xs) (targetApp t xs)))
  return r.join

/-- `∀ xs, C xs` (the ⊤ probe) or `∀ xs, ¬ C xs` (the ⊥ probe), folded. -/
def mkTrivStmt (c : ProbeTarget) (universal : Bool) : MetaM (Option Expr) := do
  let r ← attempt <| forallTelescope c.type fun xs body => do
    unless body == .sort .zero do return none
    let app := targetApp c xs
    let app := if universal then app else mkApp (mkConst ``Not) app
    return some (← mkForallFVars xs app)
  return r.join

/-!
## The probe
-/

/-- Probe context: the library grounding pool, the transparency set for
expanded forms, and domain-supplied tactic rungs (e.g. `tauto`, `aesop`
when Mathlib is ambient — they self-disable elsewhere, as in `hunt`).

`probeHeartbeats` caps each probe *attempt*'s budget (in `maxHeartbeats`
option units; `none` = ambient). Large enumerations set it low: the cheap
rungs (refl, omega, permuted simp, chain) decide well under the cap, and
what a curtailed heavy rung would have certified stays novel-so-far —
honest, and re-probeable under D3's standing obligation. -/
structure ProbeCtx where
  known : Array KnownLemma
  transparent : Name → Bool := fun n => inventedNs.isPrefixOf n
  extraRungs : Array String := #[]
  probeHeartbeats : Option Nat := none
  /-- Backward-chaining bound for the compose rung (DESIGN_DEPTH P2):
  2 on sweep ladders, deeper under escalation. -/
  composeDepth : Nat := 2
  /-- Probe implication edges at birth. Large enumerations turn this off
  and measure edges in a separate facts phase instead (with a refuter) —
  edge probes are two extra prover ladders per pair. -/
  probeEdges : Bool := true
  /-- Cap how many of the most recent live inventions a newborn is alias-
  probed against (`none` = all). The long tail belongs to the budgeted
  sweep — that is D3's standing obligation, not a silent cap; runs that
  set a window log the policy. -/
  inventedTargetWindow : Option Nat := none

/-- Run probe work under the context's per-attempt budget. Inner `attempt`s
re-baseline the counter (`withCurrHeartbeats`); the budget itself comes
from the option this sets. -/
def ProbeCtx.withBudget {α : Type} (ctx : ProbeCtx) (x : MetaM α) : MetaM α :=
  match ctx.probeHeartbeats with
  | some n => withOptions (fun o => o.set `maxHeartbeats n) x
  | none => x

/-- Corpus facts as a composition pool: discoveries prove discoveries, so
the probe's power grows with the corpus (why "novel" is only ever
"novel-so-far"). -/
def corpusKnownPool (corpus : Corpus) : MetaM (Array KnownLemma) := do
  let mut out := #[]
  for f in corpus.facts do
    if let some (binders, rel, head, head2) ← statementKey f.stmt then
      out := out.push { name := f.name, type := f.stmt, levels := [],
                        binders, rel, head, head2 }
  return out

/-- `tryTacticRung` with tactic-frontend linters silenced: probe rungs fire
speculative tactics by the hundred, and their style warnings (unused simp
arguments and the like) are noise that would otherwise leak past the
message-log restore. -/
def tryQuietRung (tac : String) (stmt : Expr) : MetaM (Option Expr) :=
  withOptions (fun o => (o.setBool `linter.all false).setBool
    `linter.unusedSimpArgs false) <| tryTacticRung tac stmt

/-- Hunt for a proof of `stmt`: the full prover ladder over the folded and
expanded forms, corpus facts included in the composition pool, then the
domain rungs. A refutation of the expanded form is a hard stop — the
statement is false, not merely unsupported. The whole hunt runs under one
outer guard: a runtime blowup anywhere (heartbeats, recursion depth) is a
failed probe, never a crashed run. -/
def probeProve (ctx : ProbeCtx) (corpus : Corpus) (stmt : Expr) :
    MetaM (Option (Expr × String)) := do
  let r ← attempt do
    let expanded ← expandConsts ctx.transparent stmt
    let pool := ctx.known ++ (← corpusKnownPool corpus)
    let corpusNames := corpus.facts.map (·.name)
    for (s, tag) in #[(stmt, "folded"), (expanded, "expanded")] do
      match ← hunt pool corpusNames s ctx.composeDepth with
      | .proved pf rung knownAs =>
        let how := match knownAs with
          | some k => s!"grounded: {k}"
          | none => s!"{rung} ({tag})"
        return some (pf, how)
      | .refuted _ => return none
      | .stillOpen => pure ()
    -- Permutative simp: conjunct/disjunct reordering (the α-equivalent-body
    -- verdict row) — terminating by ordered rewriting.
    if let some pf ← tryQuietRung
        "simp only [and_comm, and_assoc, and_left_comm, or_comm, or_assoc, or_left_comm]"
        expanded then
      return some (pf, "permuted (expanded)")
    for tac in ctx.extraRungs do
      if let some pf ← tryQuietRung tac expanded then
        return some (pf, s!"by {tac} (expanded)")
    return none
  return r.join

/-- The outcome of probing one pair. -/
inductive PairResult where
  | isAlias (proof : Expr) (how : String)
  | edges (fwd bwd : Option (Expr × String))

/-- Probe `c` against `t`: direct iff ladder, per-pair `unfold` rungs, a
transitive chain through the library, then the two directions separately
(both certified → alias by `Iff.intro`; one → a specializes/generalizes
edge). Caller commits whatever comes back; nothing here touches the
corpus or the pool. -/
def probePair (ctx : ProbeCtx) (corpus : Corpus) (c t : ProbeTarget)
    (edges : Bool := true) : MetaM PairResult := do
  let r ← attempt do
    let some iffStmt ← mkIffStmt c t
      | return PairResult.edges none none
    -- Direct ladder on the iff.
    if let some (pf, how) ← probeProve ctx corpus iffStmt then
      return PairResult.isAlias pf how
    -- Per-pair unfold rungs (the shape that grounded the baseline's tower:
    -- `unfold; rfl`, `unfold; aesop`).
    for base in #["rfl"] ++ ctx.extraRungs do
      if let some pf ← tryQuietRung s!"unfold {c.name} {t.name}; {base}" iffStmt then
        return PairResult.isAlias pf s!"by unfold; {base}"
    -- Transitive grounding: one library bridge away.
    let subProve := fun (subStmt : Expr) => do
      let expandedSub ← expandConsts ctx.transparent subStmt
      if let some pf ← tryRefl expandedSub then return some pf
      if let some pf ← trySimpWith #[] true expandedSub then return some pf
      for base in ctx.extraRungs do
        if let some pf ← tryQuietRung base expandedSub then return some pf
      return (none : Option Expr)
    if let some (pf, bridge) ← tryKnownChain ctx.known iffStmt subProve then
      return PairResult.isAlias pf s!"chained via {bridge}"
    -- Directions (two more prover ladders — skipped when the caller only
    -- wants aliases).
    unless edges do return PairResult.edges none none
    let some fwdStmt ← mkImplStmt c t
      | return PairResult.edges none none
    let some bwdStmt ← mkImplStmt t c
      | return PairResult.edges none none
    let fwd ← probeProve ctx corpus fwdStmt
    let bwd ← probeProve ctx corpus bwdStmt
    if let (some (fpf, fhow), some (bpf, _)) := (fwd, bwd) then
      let combined ← attempt <| forallTelescope iffStmt fun xs _ => do
        mkLambdaFVars xs (← mkAppM ``Iff.intro #[mkAppN fpf xs, mkAppN bpf xs])
      if let some pf := combined then
        return PairResult.isAlias pf s!"both directions ({fhow})"
    return PairResult.edges fwd bwd
  return r.getD (.edges none none)

/-- The certificate-backed verdict for a newborn concept (DESIGN_INVENT D4). -/
inductive ConceptVerdict where
  | degenerate (universal : Bool) (fact : Fact)
  | aliasOf (target : Name) (bridge : Fact) (how : String)
  | novel (specializes generalizes : Array (Name × Fact))

def ConceptVerdict.describe : ConceptVerdict → String
  | .degenerate true f => s!"degenerate (⊤): {f.name}"
  | .degenerate false f => s!"degenerate (⊥): {f.name}"
  | .aliasOf t f how => s!"alias of {t} ({how}), bridge {f.name}"
  | .novel spec genl =>
    s!"novel-so-far ({spec.size} specializes, {genl.size} generalizes)"

/-- Commit a probe result as a fact against its *folded* statement — the
proof may be of the expanded form; they are defeq and the gate checks up
to defeq. -/
def commitProbeFact (corpus : Corpus) (base : String) (stmt pf : Expr) :
    MetaM (Option (Corpus × Fact)) := do
  let nm ← freshName (.mkSimple base)
  match ← commitFact { name := nm, stmt, proof := pf } with
  | some f => return some ({ corpus with facts := corpus.facts.push f }, f)
  | none => return none

/-- Identity probe at birth: ⊤/⊥ first (the degeneracy AM never priced),
then alias against canonical targets and earlier live inventions — merge
is tombstone + bridge — then certified implication edges. Every
certificate goes through `commitFact`. -/
def probeConcept (ctx : ProbeCtx) (pool : ConceptPool) (corpus : Corpus)
    (c : Concept) (canonical : Array ProbeTarget) :
    MetaM (ConceptPool × Corpus × ConceptVerdict) := do
  let cT := c.toTarget
  let short := c.name.getString!
  -- ⊤/⊥: an alias to a trivial predicate, caught by the same machinery.
  for universal in [true, false] do
    if let some stmt ← mkTrivStmt cT universal then
      if let some (pf, _) ← ctx.withBudget <| probeProve ctx corpus stmt then
        let tag := if universal then "univ" else "empty"
        if let some (corpus', f) ← commitProbeFact corpus s!"{short}_{tag}" stmt pf then
          return (pool.merge c.name (if universal then `True else `False),
                  corpus', .degenerate universal f)
  -- Alias / edges against canonical targets first, then earlier inventions
  -- (the most recent window when one is configured; the tail is the
  -- sweep's job).
  let inventedAll := (pool.live.filter (·.name != c.name)).map (·.toTarget)
  let inventedTs := match ctx.inventedTargetWindow with
    | some k =>
      if inventedAll.size > k then
        inventedAll.extract (inventedAll.size - k) inventedAll.size
      else inventedAll
    | none => inventedAll
  let mut spec : Array (Name × Fact) := #[]
  let mut genl : Array (Name × Fact) := #[]
  let mut corpus := corpus
  for t in canonical ++ inventedTs do
    unless ← targetsCompatible cT t do continue
    let r ← ctx.withBudget <| withCurrHeartbeats <|
      probePair ctx corpus cT t ctx.probeEdges
    match r with
    | .isAlias pf how =>
      let some iffStmt ← mkIffStmt cT t | continue
      if let some (corpus', f) ←
          commitProbeFact corpus s!"{short}_alias_{t.name.getString!}" iffStmt pf then
        return (pool.merge c.name t.name, corpus', .aliasOf t.name f how)
    | .edges fwd bwd =>
      if let some (pf, _) := fwd then
        if let some fwdStmt ← mkImplStmt cT t then
          if let some (corpus', f) ←
              commitProbeFact corpus s!"{short}_imp_{t.name.getString!}" fwdStmt pf then
            corpus := corpus'
            spec := spec.push (t.name, f)
      if let some (pf, _) := bwd then
        if let some bwdStmt ← mkImplStmt t cT then
          if let some (corpus', f) ←
              commitProbeFact corpus s!"{t.name.getString!}_imp_{short}" bwdStmt pf then
            corpus := corpus'
            genl := genl.push (t.name, f)
  return (pool, corpus, .novel spec genl)

/-!
## Identity as a standing obligation (DESIGN_INVENT D3)
-/

/-- Trigger (i): a newly admitted fact mentions two or more live invented
predicates — re-probe those pairs, with the fact now in the corpus. The
younger concept merges into the elder. Cheap name-occurrence scan; probes
only fire on mentioned pairs. -/
def reprobeOnFact (ctx : ProbeCtx) (pool : ConceptPool) (corpus : Corpus)
    (f : Fact) : MetaM (ConceptPool × Corpus × Array (Name × Name)) := do
  let used := f.stmt.getUsedConstants
  let mentioned := pool.live.filter fun c => used.contains c.name
  if mentioned.size < 2 then return (pool, corpus, #[])
  let mut pool := pool
  let mut corpus := corpus
  let mut merges : Array (Name × Name) := #[]
  for i in [0 : mentioned.size] do
    for j in [i + 1 : mentioned.size] do
      let elder := mentioned[i]!
      let younger := mentioned[j]!
      unless pool.isLive elder.name && pool.isLive younger.name do continue
      unless ← targetsCompatible younger.toTarget elder.toTarget do continue
      let r ← ctx.withBudget <| withCurrHeartbeats <|
        probePair ctx corpus younger.toTarget elder.toTarget (edges := false)
      if let .isAlias pf _ := r then
        let some iffStmt ← mkIffStmt younger.toTarget elder.toTarget | continue
        let base := s!"{younger.name.getString!}_alias_{elder.name.getString!}"
        if let some (corpus', _) ← commitProbeFact corpus base iffStmt pf then
          corpus := corpus'
          pool := pool.merge younger.name elder.name
          merges := merges.push (younger.name, elder.name)
  return (pool, corpus, merges)

/-- Trigger (ii): the budgeted sweep. Enumerate (live concept × earlier
target) pairs in a deterministic order, resume at `cursor`, spend at most
`budget` probes after the compatibility prefilter, and merge what
certifies. O(n²) pairs exist; the budget is what keeps a generation's
sweep bounded — uncovered pairs wait for the next call, no silent
skipping. Returns the new cursor. -/
def sweepReprobe (ctx : ProbeCtx) (pool : ConceptPool) (corpus : Corpus)
    (canonical : Array ProbeTarget) (budget : Nat) (cursor : Nat) :
    MetaM (ConceptPool × Corpus × Array (Name × Name) × Nat) := do
  let live := pool.live
  let mut pairs : Array (Name × ProbeTarget) := #[]
  for j in [0 : live.size] do
    for t in canonical do
      pairs := pairs.push (live[j]!.name, t)
    for i in [0 : j] do
      pairs := pairs.push (live[j]!.name, live[i]!.toTarget)
  if pairs.isEmpty then return (pool, corpus, #[], 0)
  let mut pool := pool
  let mut corpus := corpus
  let mut merges : Array (Name × Name) := #[]
  let mut spent := 0
  let mut k := cursor % pairs.size
  let mut visited := 0
  while spent < budget && visited < pairs.size do
    let (cn, t) := pairs[k]!
    k := (k + 1) % pairs.size
    visited := visited + 1
    let some c := pool.find? cn | continue
    unless c.mergedInto.isNone do continue
    -- a target that is itself a merged invention is skipped
    if (pool.find? t.name).any (·.mergedInto.isSome) then continue
    unless ← targetsCompatible c.toTarget t do continue
    spent := spent + 1
    let r ← ctx.withBudget <| withCurrHeartbeats <|
      probePair ctx corpus c.toTarget t (edges := false)
    if let .isAlias pf _ := r then
      let some iffStmt ← mkIffStmt c.toTarget t | continue
      let base := s!"{c.name.getString!}_alias_{t.name.getString!}"
      if let some (corpus', _) ← commitProbeFact corpus base iffStmt pf then
        corpus := corpus'
        pool := pool.merge c.name t.name
        merges := merges.push (c.name, t.name)
  return (pool, corpus, merges, k)

/-- The invented names a statement's refuter must `unfold`, *transitively
closed*: a depth-2 concept's body mentions its depth-1 parent, which
simp cannot unfold either (no equation lemmas for gate-declared defs).
Found by the benchmark arc — a statement mentioning only the lift was
irrefutable because its parent stayed folded. -/
def inventedUnfoldNames (stmt : Expr) : MetaM (Array Name) := do
  let mut out : Array Name := #[]
  let mut frontier := stmt.getUsedConstants.filter (inventedNs.isPrefixOf ·)
  while !frontier.isEmpty do
    let mut next : Array Name := #[]
    for n in frontier do
      unless out.contains n do
        out := out.push n
        if let some ci := (← getEnv).find? n then
          if let some v := ci.value? then
            for m in v.getUsedConstants do
              if inventedNs.isPrefixOf m && !out.contains m &&
                  !next.contains m then
                next := next.push m
    frontier := next
  return out

/-- The `unfold` prefix for invented-aware refuters, from the transitive
closure; empty when the statement mentions no invented vocabulary. -/
def inventedUnfoldPre (stmt : Expr) : MetaM String := do
  let ns ← inventedUnfoldNames stmt
  if ns.isEmpty then return ""
  return s!"unfold {String.intercalate " " (ns.map toString).toList}; "

/-- Judge a conjecture phrased in invented vocabulary: `judge`'s hunt sees
invented constants as opaque, so the prover here is `probeProve` (folded +
delta-expanded forms) and the proof commits against the folded statement.
The refuter contract is `judge`'s: a refutation is a kernel fact — the
negated instance — admitted through the gate; the caller supplies a
refuter that can see through the vocabulary (e.g. `unfold`-prefixed). -/
def judgeConceptFact (ctx : ProbeCtx) (corpus : Corpus) (c : Conjecture)
    (refuter : Refuter := fun _ => pure none) :
    MetaM (Corpus × Outcome) := withCurrHeartbeats do
  if let some (negStmt, pf, witness) ← refuter c.stmt then
    let nm ← freshName (c.name.appendAfter "_refuted")
    let p : FactProposal := { name := nm, stmt := negStmt, proof := pf,
                              origin := c.origin, rung := s!"refuted: {witness}" }
    if let some f ← commitFact p then
      return ({ corpus with facts := corpus.facts.push f }, .refuted witness)
  if let some (pf, how) ← ctx.withBudget <| probeProve ctx corpus c.stmt then
    let nm ← freshName c.name
    match ← commitFact { name := nm, stmt := c.stmt, proof := pf,
                         origin := c.origin, rung := how } with
    | some f =>
      return ({ corpus with facts := corpus.facts.push f }, .admitted f how)
    | none => return (corpus, .refusedAtGate)
  return (corpus, .stillOpen)

/-- The escalation judge (DESIGN_DEPTH P1/P2): refuter first, then the
deep ladder — `probeProve` under the deep context (expansion-aware, so it
handles invented and canonical statements alike; widened pool, uncut
rungs, deeper composition), then the induction rungs against the closed
statement. Successes commit through the ordinary gates; the rung note is
prefixed `escalated:` for the tier classifier. -/
def escalate (deep : ProbeCtx) (corpus : Corpus) (c : Conjecture)
    (refuter : Refuter := fun _ => pure none)
    (inductionRungs : Array String :=
      #["intro a; induction a <;> simp_all",
        "intro a; induction a <;> simp_all <;> omega",
        "intro a b; induction a <;> simp_all <;> omega"]) :
    MetaM (Corpus × Outcome) := withCurrHeartbeats do
  if let some (negStmt, pf, witness) ← refuter c.stmt then
    let nm ← freshName (c.name.appendAfter "_refuted")
    let p : FactProposal := { name := nm, stmt := negStmt, proof := pf,
                              origin := c.origin, rung := s!"refuted: {witness}" }
    if let some f ← commitFact p then
      return ({ corpus with facts := corpus.facts.push f }, .refuted witness)
  if let some (pf, how) ← deep.withBudget <| probeProve deep corpus c.stmt then
    let nm ← freshName c.name
    let p : FactProposal := { name := nm, stmt := c.stmt, proof := pf,
                              origin := c.origin, rung := s!"escalated: {how}" }
    if let some f ← commitFact p then
      return ({ corpus with facts := corpus.facts.push f },
              .admitted f s!"escalated: {how}")
  for tac in inductionRungs do
    if let some pf ← tryTacticClosed tac c.stmt then
      let nm ← freshName c.name
      let p : FactProposal := { name := nm, stmt := c.stmt, proof := pf,
                                origin := c.origin, rung := "escalated: induction" }
      if let some f ← commitFact p then
        return ({ corpus with facts := corpus.facts.push f },
                .admitted f "escalated: induction")
  return (corpus, .stillOpen)

/-!
## Generative operators (DESIGN_INVENT D5, slice one)

Conjunction and negated-conjunct over comparable `Prop`-valued targets.
Dualization and singleton-lift are domain-shaped and live with the
domains. Invented concepts do not re-enter the operator pool here —
compounding is slice two.
-/

/-- `fun xs => P xs ∧ Q xs`, or `P xs ∧ ¬ Q xs` when `negated`. -/
def mkConjProposal (negated : Bool) (p q : ProbeTarget) :
    MetaM (Option ConceptProposal) := do
  unless ← targetsCompatible p q do return none
  let r ← attempt <| forallTelescope p.type fun xs body => do
    unless body == .sort .zero do return none
    let lhs := targetApp p xs
    let rhs := targetApp q xs
    let rhs := if negated then mkApp (mkConst ``Not) rhs else rhs
    let value ← mkLambdaFVars xs (mkApp2 (mkConst ``And) lhs rhs)
    let type ← mkForallFVars xs (.sort .zero)
    let mid := if negated then "and_not" else "and"
    return some { name := .mkSimple s!"{p.name.getString!}_{mid}_{q.name.getString!}",
                  type, value, origin := if negated then `negConj else `conj }
  return r.join

/-- The slice-one yield-curve metrics (DESIGN_INVENT D5): fixed in advance, per
run. -/
structure InventStats where
  candidates : Nat := 0
  refused : Nat := 0
  degenerate : Nat := 0
  aliased : Nat := 0
  novel : Nat := 0
  edgeFacts : Nat := 0

def InventStats.describe (s : InventStats) : String :=
  s!"{s.candidates} candidates: {s.refused} refused at birth, \
{s.degenerate} degenerate, {s.aliased} merged as aliases, \
{s.novel} novel-so-far, {s.edgeFacts} certified spec/genl edges"

/-- One candidate's fate at the birth gate — a refusal reason or a
verdict. Callers that speak back to a proposer (the concept booth) build
their feedback from these. -/
structure BirthReport where
  name : Name
  outcome : Except String ConceptVerdict

/-- Drive one batch of candidates through the lifecycle: birth gate,
identity probe, verdict. Logs one line per candidate; refusals carry
their reasons. Returns per-candidate reports alongside the stats. -/
def inventRoundWith (ctx : ProbeCtx) (pool : ConceptPool) (corpus : Corpus)
    (canonical : Array ProbeTarget) (proposals : Array ConceptProposal) :
    MetaM (ConceptPool × Corpus × InventStats × Array BirthReport) := do
  let mut pool := pool
  let mut corpus := corpus
  let mut stats : InventStats := {}
  let mut reports : Array BirthReport := #[]
  for p in proposals do
    stats := { stats with candidates := stats.candidates + 1 }
    match ← commitConcept pool p with
    | .error reason =>
      stats := { stats with refused := stats.refused + 1 }
      reports := reports.push ⟨p.name, .error reason⟩
      IO.println s!"  ! {p.name} — refused at birth: {reason}"
    | .ok (pool', c) =>
      pool := pool'
      let (pool'', corpus', verdict) ←
        withCurrHeartbeats <| probeConcept ctx pool corpus c canonical
      pool := pool''
      corpus := corpus'
      reports := reports.push ⟨p.name, .ok verdict⟩
      match verdict with
      | .degenerate _ _ =>
        stats := { stats with degenerate := stats.degenerate + 1 }
        IO.println s!"  ⊥ {c.name} — {verdict.describe}"
      | .aliasOf _ _ _ =>
        stats := { stats with aliased := stats.aliased + 1 }
        IO.println s!"  ≡ {c.name} — {verdict.describe}"
      | .novel spec genl =>
        stats := { stats with
          novel := stats.novel + 1
          edgeFacts := stats.edgeFacts + spec.size + genl.size }
        IO.println s!"  ✦ {c.name} — {verdict.describe}"
  return (pool, corpus, stats, reports)

/-- `inventRoundWith`, reports dropped. -/
def inventRound (ctx : ProbeCtx) (pool : ConceptPool) (corpus : Corpus)
    (canonical : Array ProbeTarget) (proposals : Array ConceptProposal) :
    MetaM (ConceptPool × Corpus × InventStats) := do
  let (pool, corpus, stats, _) ←
    inventRoundWith ctx pool corpus canonical proposals
  return (pool, corpus, stats)

end Runtime
end Eureka
