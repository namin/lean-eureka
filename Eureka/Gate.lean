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

In the running system (`Eureka.Runtime`), `World.Stmt` is a `Prop`-typed
`Expr`, the gate is the Lean kernel, and heuristic code is a metaprogram.
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
for the gate, or a brand-new heuristic, given as code. Proposing code is the
EURISKO move: heuristics that create heuristics. -/
inductive Proposal (W : World) (G : Gate W) (Code : Type) : Type where
  | fact (s : W.Stmt) (e : G.Evidence)
  | rule (c : Code)

/-- Discovery state: the corpus of admitted statements and the installed
heuristics, kept as code so that installing one is an ordinary state change. -/
structure State (W : World) (G : Gate W) (Code : Type) : Type where
  corpus : List W.Stmt
  heuristics : List Code

/-- A state is sound when everything in its corpus actually holds. -/
def State.Sound {W : World} {G : Gate W} {Code : Type}
    (st : State W G Code) : Prop :=
  ∀ s ∈ st.corpus, W.Holds s

section Dynamics

variable {W : World} {G : Gate W} {Code : Type}

/-- An admission policy: how a proposal transforms the state. The three
policies below differ only here — this is the keynote's "modification kind"
axis made explicit. -/
abbrev Admission (W : World) (G : Gate W) (Code : Type) : Type :=
  State W G Code → Proposal W G Code → State W G Code

/-- Gated admission: facts enter the corpus only if the gate accepts their
evidence; heuristic code installs *unrestricted*. Deliberately so — see
`discovery_sound` for what unrestricted heuristic birth costs (nothing, for
corpus soundness) and `ruleGated_heuristics_invariant` for what gating it
would buy (policy, not soundness). -/
def admit (st : State W G Code) : Proposal W G Code → State W G Code
  | .fact s e => if G.check s e then { st with corpus := s :: st.corpus } else st
  | .rule c => { st with heuristics := c :: st.heuristics }

/-- Ungated admission — Lenat's EURISKO: proposals enter unchecked. -/
def admitUngated (st : State W G Code) : Proposal W G Code → State W G Code
  | .fact s _ => { st with corpus := s :: st.corpus }
  | .rule c => { st with heuristics := c :: st.heuristics }

/-- Rule-gated admission: like `admit`, but heuristic code must additionally
pass a policy check `P` before installation. -/
def admitRuleGated (P : Code → Bool) (st : State W G Code) :
    Proposal W G Code → State W G Code
  | .fact s e => if G.check s e then { st with corpus := s :: st.corpus } else st
  | .rule c => if P c then { st with heuristics := c :: st.heuristics } else st

/-- One discovery step under admission policy `adm`: an *installed* heuristic
fires — its behavior given by an arbitrary, adversarially chosen interpreter
`run` — and one of its proposals is admitted. -/
inductive Step (adm : Admission W G Code)
    (run : Code → State W G Code → List (Proposal W G Code)) :
    State W G Code → State W G Code → Prop where
  | fire {st : State W G Code} {c : Code} {p : Proposal W G Code}
      (hc : c ∈ st.heuristics) (hp : p ∈ run c st) :
      Step adm run st (adm st p)

/-- Reachability: any finite interleaving of steps. -/
inductive Reachable (adm : Admission W G Code)
    (run : Code → State W G Code → List (Proposal W G Code)) :
    State W G Code → State W G Code → Prop where
  | refl (st : State W G Code) : Reachable adm run st st
  | tail {st₁ st₂ st₃ : State W G Code} :
      Reachable adm run st₁ st₂ → Step adm run st₂ st₃ →
      Reachable adm run st₁ st₃

/-- Any property preserved by the admission policy is invariant along
reachability — the workhorse behind every theorem below. -/
theorem Reachable.invariant {adm : Admission W G Code}
    {run : Code → State W G Code → List (Proposal W G Code)}
    {I : State W G Code → Prop}
    (hadm : ∀ (st : State W G Code) (p : Proposal W G Code), I st → I (adm st p))
    {st₁ st₂ : State W G Code}
    (h : Reachable adm run st₁ st₂) (hI : I st₁) : I st₂ := by
  induction h with
  | refl => exact hI
  | tail _ hstep ih =>
    cases hstep with
    | fire _ _ => exact hadm _ _ ih

/-- Anything in the corpus after a gated admission was already there, or
carries gate-accepted evidence. -/
theorem admit_corpus_sub {st : State W G Code} (p : Proposal W G Code) :
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

/-- Gated admission preserves soundness. -/
theorem admit_sound {st : State W G Code} (h : st.Sound)
    (p : Proposal W G Code) : (admit st p).Sound := fun s hs =>
  match admit_corpus_sub p s hs with
  | .inl hmem => h s hmem
  | .inr ⟨e, hce⟩ => G.sound s e hce

/-- **Corpus soundness needs only the object gate.** For arbitrary heuristic
code, an arbitrary (adversarial) interpreter, and unrestricted heuristic
birth — heuristics creating heuristics creating heuristics — every state
reachable from a sound seed is sound. -/
theorem discovery_sound
    {run : Code → State W G Code → List (Proposal W G Code)}
    {seed st : State W G Code} (hseed : seed.Sound)
    (h : Reachable admit run seed st) : st.Sound :=
  h.invariant (I := State.Sound) (fun _ p h' => admit_sound h' p) hseed

/-- **Provenance.** Everything in a reachable corpus is either seed or
entered through the gate: some evidence for it was checked and accepted. -/
theorem discovery_provenance
    {run : Code → State W G Code → List (Proposal W G Code)}
    {seed st : State W G Code}
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
    {st : State W G Code} (p : Proposal W G Code) :
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

/-- **What gating heuristic birth buys: policy, not soundness.** Under a
rule-gated admission, any policy `P` satisfied by the seed heuristics is an
invariant of the heuristic population, for every reachable state. (Corpus
soundness never needed this — `discovery_sound`.) -/
theorem ruleGated_heuristics_invariant {P : Code → Bool}
    {run : Code → State W G Code → List (Proposal W G Code)}
    {seed st : State W G Code}
    (hseed : ∀ c ∈ seed.heuristics, P c = true)
    (h : Reachable (admitRuleGated P) run seed st) :
    ∀ c ∈ st.heuristics, P c = true := by
  refine h.invariant (I := fun st' => ∀ c ∈ st'.heuristics, P c = true)
    ?_ hseed
  intro st' p ih c hc
  match admitRuleGated_heuristics_sub p c hc with
  | .inl hmem => exact ih c hmem
  | .inr hPc => exact hPc

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

/-- The malicious interpreter: every firing proposes `False`, with junk
evidence. -/
def run : Code → State W G Code → List (Proposal W G Code) :=
  fun _ _ => [.fact False ()]

/-- Seed: empty corpus, one installed heuristic. Vacuously sound. -/
def seed : State W G Code := { corpus := [], heuristics := [()] }

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
theorem gated_immune {st : State W G Code}
    (h : Reachable admit run seed st) : st.Sound :=
  discovery_sound seed_sound h

end UngatedCollapse

end Eureka
