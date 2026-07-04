/-!
# The discovery gate, in the small

A minimal model of a EURISKO-style discovery loop in which heuristics are
arbitrary untrusted code — including code that creates new heuristics, which
create new heuristics in turn — and the only trusted component is a gate that
checks evidence before a statement enters the corpus.

Main results:

* `Eureka.discovery_sound` — corpus soundness needs only the object-level
  gate: for an arbitrary (adversarial) interpreter of heuristic code and
  **unrestricted** heuristic birth, every state reachable from a sound seed
  has a sound corpus.
* `Eureka.discovery_provenance` — everything in a reachable corpus is either
  seed or entered through the gate with accepted evidence.
* `Eureka.UngatedCollapse.ungated_reaches_unsound` — remove the gate (Lenat's
  original regime) and a single firing of a malicious heuristic corrupts the
  corpus; `Eureka.UngatedCollapse.gated_immune` shows the same seed under the
  same malicious interpreter is harmless behind the gate.
* `Eureka.ruleGated_heuristics_invariant` — what gating *heuristic birth*
  buys is not soundness (which `discovery_sound` gets without it) but policy
  invariants over the heuristic population.
* `Eureka.concept_birth_conservative` / `Eureka.concept_birth_sound` —
  concept birth is a conservative extension: installing an invented
  definition never touches the corpus, so it preserves soundness outright.
  A concept here is a *name for an already-expressible statement-former*
  (in the runtime, a delta-expandable `def`), so `Holds` needs no change.
* `Eureka.defGated_sound` / `Eureka.defGated_concepts_invariant` — gating
  concept birth (the runtime's screen + kernel + reserved-namespace audit)
  keeps soundness and buys the same kind of policy invariant over the
  concept population that `ruleGated_heuristics_invariant` buys over
  heuristics: every installed concept passed the def gate.

In the running system (`Eureka.Runtime`), `World.Stmt` is a `Prop`-typed
`Expr`, the intended gate is Lean kernel checking plus an axiom audit, and
heuristic code is a metaprogram. The runtime instantiates this model by
construction and inspection; there is no formal refinement proof from the
`MetaM` implementation to this model. The gates themselves are fixed here —
making the gate reflectively modifiable through a gate one level up is
lean-keep's axis.
-/

namespace Eureka

/-- A domain of discourse: statements together with ground truth. In the
running system `Stmt` is `Expr` and `Holds` is truth in the ambient theory;
here both are abstract. -/
structure World where
  Stmt : Type
  Holds : Stmt → Prop

/-- The trusted gate: an evidence checker, sound for the world. In the
running system this is the Lean kernel — `Evidence` is a proof term and
`check` is type checking. Everything else in the model is untrusted. -/
structure Gate (W : World) where
  Evidence : Type
  check : W.Stmt → Evidence → Bool
  sound : ∀ s e, check s e = true → W.Holds s

/-- What untrusted heuristic code may propose: a fact together with evidence
for the gate, a brand-new heuristic, given as code — the EURISKO move:
heuristics that create heuristics — or a brand-new *concept*: an invented
definition. A concept names a statement-former the world can already
express (in the runtime, a delta-expandable `def`), so proposing one never
touches ground truth; what it changes is which statements later proposals
are phrased in. -/
inductive Proposal (W : World) (G : Gate W) (Code : Type) (Concept : Type) :
    Type where
  | fact (s : W.Stmt) (e : G.Evidence)
  | rule (c : Code)
  | concept (d : Concept)

/-- Discovery state: the corpus of admitted statements, the installed
heuristics (kept as code so that installing one is an ordinary state
change), and the invented concepts — corpus-adjacent vocabulary, not
facts. -/
structure State (W : World) (G : Gate W) (Code : Type) (Concept : Type) :
    Type where
  corpus : List W.Stmt
  heuristics : List Code
  concepts : List Concept

/-- A state is sound when everything in its corpus actually holds. Concepts
do not appear here: an invented definition asserts nothing. -/
def State.Sound {W : World} {G : Gate W} {Code : Type} {Concept : Type}
    (st : State W G Code Concept) : Prop :=
  ∀ s ∈ st.corpus, W.Holds s

section Dynamics

variable {W : World} {G : Gate W} {Code : Type} {Concept : Type}

/-- An admission policy: how a proposal transforms the state. The three
policies below differ only here — this is the keynote's "modification kind"
axis made explicit. -/
abbrev Admission (W : World) (G : Gate W) (Code : Type) (Concept : Type) :
    Type :=
  State W G Code Concept → Proposal W G Code Concept → State W G Code Concept

/-- Gated admission: facts enter the corpus only if the gate accepts their
evidence; heuristic code and concepts install *unrestricted*. Deliberately
so — see `discovery_sound` for what unrestricted heuristic and concept
birth costs (nothing, for corpus soundness), and the `ruleGated`/`defGated`
invariants for what gating them buys (policy, not soundness). -/
def admit (st : State W G Code Concept) :
    Proposal W G Code Concept → State W G Code Concept
  | .fact s e => if G.check s e then { st with corpus := s :: st.corpus } else st
  | .rule c => { st with heuristics := c :: st.heuristics }
  | .concept d => { st with concepts := d :: st.concepts }

/-- Ungated admission — Lenat's EURISKO: proposals enter unchecked. -/
def admitUngated (st : State W G Code Concept) :
    Proposal W G Code Concept → State W G Code Concept
  | .fact s _ => { st with corpus := s :: st.corpus }
  | .rule c => { st with heuristics := c :: st.heuristics }
  | .concept d => { st with concepts := d :: st.concepts }

/-- Rule-gated admission: like `admit`, but heuristic code must additionally
pass a policy check `P` before installation. -/
def admitRuleGated (P : Code → Bool) (st : State W G Code Concept) :
    Proposal W G Code Concept → State W G Code Concept
  | .fact s e => if G.check s e then { st with corpus := s :: st.corpus } else st
  | .rule c => if P c then { st with heuristics := c :: st.heuristics } else st
  | .concept d => { st with concepts := d :: st.concepts }

/-- Def-gated admission: like `admit`, but a concept must additionally pass
a well-formedness check `D` before installation. In the runtime `D` is the
concept screen plus the kernel's check of the definition plus the
reserved-namespace audit. -/
def admitDefGated (D : Concept → Bool) (st : State W G Code Concept) :
    Proposal W G Code Concept → State W G Code Concept
  | .fact s e => if G.check s e then { st with corpus := s :: st.corpus } else st
  | .rule c => { st with heuristics := c :: st.heuristics }
  | .concept d => if D d then { st with concepts := d :: st.concepts } else st

/-- One discovery step under admission policy `adm`: an *installed* heuristic
fires — its behavior given by an arbitrary, adversarially chosen interpreter
`run` — and one of its proposals is admitted. -/
inductive Step (adm : Admission W G Code Concept)
    (run : Code → State W G Code Concept → List (Proposal W G Code Concept)) :
    State W G Code Concept → State W G Code Concept → Prop where
  | fire {st : State W G Code Concept} {c : Code} {p : Proposal W G Code Concept}
      (hc : c ∈ st.heuristics) (hp : p ∈ run c st) :
      Step adm run st (adm st p)

/-- Reachability: any finite interleaving of steps. -/
inductive Reachable (adm : Admission W G Code Concept)
    (run : Code → State W G Code Concept → List (Proposal W G Code Concept)) :
    State W G Code Concept → State W G Code Concept → Prop where
  | refl (st : State W G Code Concept) : Reachable adm run st st
  | tail {st₁ st₂ st₃ : State W G Code Concept} :
      Reachable adm run st₁ st₂ → Step adm run st₂ st₃ →
      Reachable adm run st₁ st₃

/-- Any property preserved by the admission policy is invariant along
reachability — the workhorse behind every theorem below. -/
theorem Reachable.invariant {adm : Admission W G Code Concept}
    {run : Code → State W G Code Concept → List (Proposal W G Code Concept)}
    {I : State W G Code Concept → Prop}
    (hadm : ∀ (st : State W G Code Concept) (p : Proposal W G Code Concept),
      I st → I (adm st p))
    {st₁ st₂ : State W G Code Concept}
    (h : Reachable adm run st₁ st₂) (hI : I st₁) : I st₂ := by
  induction h with
  | refl => exact hI
  | tail _ hstep ih =>
    cases hstep with
    | fire _ _ => exact hadm _ _ ih

/-- Anything in the corpus after a gated admission was already there, or
carries gate-accepted evidence. -/
theorem admit_corpus_sub {st : State W G Code Concept}
    (p : Proposal W G Code Concept) :
    ∀ s ∈ (admit st p).corpus, s ∈ st.corpus ∨ ∃ e, G.check s e = true := by
  match p with
  | .fact s₀ e₀ =>
    intro s hs
    cases hce : G.check s₀ e₀ with
    | true =>
      rw [admit, if_pos hce] at hs
      cases hs with
      | head => exact .inr ⟨e₀, hce⟩
      | tail _ hmem => exact .inl hmem
    | false =>
      rw [admit, if_neg (fun h => Bool.noConfusion (hce.symm.trans h))] at hs
      exact .inl hs
  | .rule c => intro s hs; exact .inl hs
  | .concept d => intro s hs; exact .inl hs

/-- Gated admission preserves soundness. -/
theorem admit_sound {st : State W G Code Concept} (h : st.Sound)
    (p : Proposal W G Code Concept) : (admit st p).Sound := fun s hs =>
  match admit_corpus_sub p s hs with
  | .inl hmem => h s hmem
  | .inr ⟨e, hce⟩ => G.sound s e hce

/-- **Concept birth is a conservative extension.** Installing an invented
definition leaves the corpus untouched — definitionally. This is the
model-level content of "a `def` is delta-expandable": the concept adds a
name, not a truth. -/
theorem concept_birth_conservative {st : State W G Code Concept}
    (d : Concept) : (admit st (.concept d)).corpus = st.corpus := rfl

/-- **Concept birth preserves corpus soundness** — immediately, by
conservativity. -/
theorem concept_birth_sound {st : State W G Code Concept} (h : st.Sound)
    (d : Concept) : (admit st (.concept d)).Sound := fun s hs => h s hs

/-- **Corpus soundness needs only the object gate.** For arbitrary heuristic
code, an arbitrary (adversarial) interpreter, and unrestricted heuristic
birth — heuristics creating heuristics creating heuristics — every state
reachable from a sound seed is sound. -/
theorem discovery_sound
    {run : Code → State W G Code Concept → List (Proposal W G Code Concept)}
    {seed st : State W G Code Concept} (hseed : seed.Sound)
    (h : Reachable admit run seed st) : st.Sound :=
  h.invariant (I := State.Sound) (fun _ p h' => admit_sound h' p) hseed

/-- **Provenance.** Everything in a reachable corpus is either seed or
entered through the gate: some evidence for it was checked and accepted.
Statements phrased in invented concept vocabulary are not special here —
a concept names a statement the world could already express, so
concept-vocabulary facts carry gate-checked evidence like any other. -/
theorem discovery_provenance
    {run : Code → State W G Code Concept → List (Proposal W G Code Concept)}
    {seed st : State W G Code Concept}
    (h : Reachable admit run seed st) :
    ∀ s ∈ st.corpus, s ∈ seed.corpus ∨ ∃ e, G.check s e = true := by
  refine h.invariant (I := fun st' =>
    ∀ s ∈ st'.corpus, s ∈ seed.corpus ∨ ∃ e, G.check s e = true)
    ?_ (fun s hs => .inl hs)
  intro st' p ih s hs
  match admit_corpus_sub p s hs with
  | .inl hmem => exact ih s hmem
  | .inr hev => exact .inr hev

/-- Heuristics installed under a rule gate all passed it. -/
theorem admitRuleGated_heuristics_sub {P : Code → Bool}
    {st : State W G Code Concept} (p : Proposal W G Code Concept) :
    ∀ c ∈ (admitRuleGated P st p).heuristics,
      c ∈ st.heuristics ∨ P c = true := by
  match p with
  | .fact s₀ e₀ =>
    intro c hc
    cases hce : G.check s₀ e₀ with
    | true =>
      rw [admitRuleGated, if_pos hce] at hc
      exact .inl hc
    | false =>
      rw [admitRuleGated, if_neg (fun h => Bool.noConfusion (hce.symm.trans h))] at hc
      exact .inl hc
  | .rule c₀ =>
    intro c hc
    cases hPc : P c₀ with
    | true =>
      rw [admitRuleGated, if_pos hPc] at hc
      cases hc with
      | head => exact .inr hPc
      | tail _ hmem => exact .inl hmem
    | false =>
      rw [admitRuleGated, if_neg (fun h => Bool.noConfusion (hPc.symm.trans h))] at hc
      exact .inl hc
  | .concept d => intro c hc; exact .inl hc

/-- **What gating heuristic birth buys: policy, not soundness.** Under a
rule-gated admission, any policy `P` satisfied by the seed heuristics is an
invariant of the heuristic population, for every reachable state. (Corpus
soundness never needed this — `discovery_sound`.) -/
theorem ruleGated_heuristics_invariant {P : Code → Bool}
    {run : Code → State W G Code Concept → List (Proposal W G Code Concept)}
    {seed st : State W G Code Concept}
    (hseed : ∀ c ∈ seed.heuristics, P c = true)
    (h : Reachable (admitRuleGated P) run seed st) :
    ∀ c ∈ st.heuristics, P c = true := by
  refine h.invariant (I := fun st' => ∀ c ∈ st'.heuristics, P c = true)
    ?_ hseed
  intro st' p ih c hc
  match admitRuleGated_heuristics_sub p c hc with
  | .inl hmem => exact ih c hmem
  | .inr hPc => exact hPc

/-- Facts admitted under the def gate went through the object gate exactly
as under `admit`. -/
theorem admitDefGated_corpus_sub {D : Concept → Bool}
    {st : State W G Code Concept} (p : Proposal W G Code Concept) :
    ∀ s ∈ (admitDefGated D st p).corpus,
      s ∈ st.corpus ∨ ∃ e, G.check s e = true := by
  match p with
  | .fact s₀ e₀ =>
    intro s hs
    cases hce : G.check s₀ e₀ with
    | true =>
      rw [admitDefGated, if_pos hce] at hs
      cases hs with
      | head => exact .inr ⟨e₀, hce⟩
      | tail _ hmem => exact .inl hmem
    | false =>
      rw [admitDefGated, if_neg (fun h => Bool.noConfusion (hce.symm.trans h))] at hs
      exact .inl hs
  | .rule c => intro s hs; exact .inl hs
  | .concept d₀ =>
    intro s hs
    cases hDd : D d₀ with
    | true =>
      rw [admitDefGated, if_pos hDd] at hs
      exact .inl hs
    | false =>
      rw [admitDefGated, if_neg (fun h => Bool.noConfusion (hDd.symm.trans h))] at hs
      exact .inl hs

/-- **The def-gated system is still sound.** Adding the concept gate on top
of the object gate loses nothing: every state reachable from a sound seed
is sound. -/
theorem defGated_sound {D : Concept → Bool}
    {run : Code → State W G Code Concept → List (Proposal W G Code Concept)}
    {seed st : State W G Code Concept} (hseed : seed.Sound)
    (h : Reachable (admitDefGated D) run seed st) : st.Sound :=
  h.invariant (I := State.Sound)
    (fun _ p h' s hs =>
      match admitDefGated_corpus_sub p s hs with
      | .inl hmem => h' s hmem
      | .inr ⟨e, hce⟩ => G.sound s e hce)
    hseed

/-- Concepts installed under a def gate all passed it. -/
theorem admitDefGated_concepts_sub {D : Concept → Bool}
    {st : State W G Code Concept} (p : Proposal W G Code Concept) :
    ∀ d ∈ (admitDefGated D st p).concepts,
      d ∈ st.concepts ∨ D d = true := by
  match p with
  | .fact s₀ e₀ =>
    intro d hd
    cases hce : G.check s₀ e₀ with
    | true =>
      rw [admitDefGated, if_pos hce] at hd
      exact .inl hd
    | false =>
      rw [admitDefGated, if_neg (fun h => Bool.noConfusion (hce.symm.trans h))] at hd
      exact .inl hd
  | .rule c => intro d hd; exact .inl hd
  | .concept d₀ =>
    intro d hd
    cases hDd : D d₀ with
    | true =>
      rw [admitDefGated, if_pos hDd] at hd
      cases hd with
      | head => exact .inr hDd
      | tail _ hmem => exact .inl hmem
    | false =>
      rw [admitDefGated, if_neg (fun h => Bool.noConfusion (hDd.symm.trans h))] at hd
      exact .inl hd

/-- **What gating concept birth buys: policy, not soundness.** Under a
def-gated admission, any well-formedness policy `D` satisfied by the seed
concepts is an invariant of the concept population, for every reachable
state. This is the model counterpart of the runtime's reserved-namespace
audit: every invented definition in the environment is gate-admitted. -/
theorem defGated_concepts_invariant {D : Concept → Bool}
    {run : Code → State W G Code Concept → List (Proposal W G Code Concept)}
    {seed st : State W G Code Concept}
    (hseed : ∀ d ∈ seed.concepts, D d = true)
    (h : Reachable (admitDefGated D) run seed st) :
    ∀ d ∈ st.concepts, D d = true := by
  refine h.invariant (I := fun st' => ∀ d ∈ st'.concepts, D d = true)
    ?_ hseed
  intro st' p ih d hd
  match admitDefGated_concepts_sub p d hd with
  | .inl hmem => exact ih d hmem
  | .inr hDd => exact hDd

end Dynamics

/-!
## The gate is load-bearing

The same seed, the same malicious heuristic, the same interpreter: ungated,
one firing corrupts the corpus; gated, no reachable state is unsound.
-/

namespace UngatedCollapse

/-- Statements are propositions; truth is the proposition itself. -/
def W : World := { Stmt := Prop, Holds := id }

/-- A gate that accepts nothing; evidence carries no information. Sound
vacuously — nothing is ever certified. -/
def G : Gate W where
  Evidence := Unit
  check _ _ := false
  sound _ _ h := nomatch h

/-- Heuristic "code" carries no structure; all behavior lives in `run`. -/
abbrev Code : Type := Unit

/-- Concepts carry no structure either; the collapse needs neither. -/
abbrev Concept : Type := Unit

/-- The malicious interpreter: every firing proposes `False`, with junk
evidence. -/
def run : Code → State W G Code Concept → List (Proposal W G Code Concept) :=
  fun _ _ => [.fact False ()]

/-- Seed: empty corpus, one installed heuristic, no concepts. Vacuously
sound. -/
def seed : State W G Code Concept :=
  { corpus := [], heuristics := [()], concepts := [] }

theorem seed_sound : seed.Sound := fun _ hs => nomatch hs

/-- **Ungated collapse.** Without the gate, an unsound state is reachable in
one firing: the corpus comes to assert `False`. -/
theorem ungated_reaches_unsound :
    ∃ st, Reachable admitUngated run seed st ∧ ¬ st.Sound := by
  refine ⟨admitUngated seed (.fact False ()),
    .tail (.refl _) (.fire (List.Mem.head _) (List.Mem.head _)), ?_⟩
  intro h
  exact h False (List.Mem.head _)

/-- **Gated immunity.** Behind the gate, the same malicious interpreter over
the same seed never produces an unsound state. -/
theorem gated_immune {st : State W G Code Concept}
    (h : Reachable admit run seed st) : st.Sound :=
  discovery_sound seed_sound h

end UngatedCollapse

end Eureka
