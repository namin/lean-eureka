# TUTORIAL: lean-eureka as reasonable reflection

Reasonable reflection is the discipline of allowing arbitrary modification
of a system's meta level, gated by an independent kernel. The pattern has
three components — a **substrate** (the system being modified), a **gate**
(small, trusted, mechanical), and a **proposer** (human, LLM, or search,
untrusted) — and instances vary along six axes: substrate kind,
modification kind, evidence kind, policy, guarantee, reflective depth.

This tutorial walks lean-eureka as one instance of that pattern, one axis
at a time, each stop a command you can run. The lineage being answered:
Lenat's EURISKO had heuristics that create heuristics — rich, and
ungovernable, because nothing checked what a heuristic put into the theory.
Here the same expressiveness runs behind a gate, and the gate's adequacy is
itself a theorem.

For this artifact the axes read:

| axis | instance |
|---|---|
| substrate kind | a heuristic agenda over a growing corpus of statements |
| modification kind | admitting a fact; installing (or birthing) a heuristic |
| evidence kind | kernel-checked proof terms; elaboration + audit for code; alias certificates for vocabulary |
| policy | proof type-checks with bounded axiom footprint; code elaborates at the interface type, no `sorry`, effect denylist |
| guarantee | every reachable corpus is sound and gate-provenanced (`discovery_sound`, `discovery_provenance`) |
| reflective depth | heuristics birth heuristics, unrestricted; the gate-for-the-gate axis is lean-keep's, its Löbian limit lean-loeb's |

Setup: `lake build` (the core has no dependencies; ~30s cold). Sections 8–9
additionally need `lake build EurekaMathlib` (Mathlib; first build fetches
the cache). Sections marked *live* need the `aws` CLI with Bedrock access —
every live run has a deterministic, credential-free counterpart.

## 1. The guarantee, as theorems

```
lake build && lake env lean Audit.lean
```

Silence from `Audit.lean` is the point: every headline theorem depends on
**no axioms at all**, enforced by `#guard_msgs` at elaboration time.

Read `Eureka/Gate.lean` top to bottom (~250 lines). The model: a `World`
(statements + ground truth), a `Gate` (an evidence checker, sound by
assumption — in the running system this is Lean's kernel), and a `State`
holding a corpus and a population of heuristics *as code*. A `Step` fires
an installed heuristic under an **adversarially chosen** interpreter and
admits one of its proposals: a fact with evidence, or a new heuristic.

Three theorems carry the artifact:

- `discovery_sound` — with the object gate alone, heuristic birth
  completely **unrestricted**, every state reachable from a sound seed has
  a sound corpus. Corpus soundness never needed the meta level governed.
- `UngatedCollapse.ungated_reaches_unsound` — delete the gate (Lenat's
  regime) and the same seed, same malicious heuristic, asserts `False` in
  one firing. `gated_immune` is the same scenario behind the gate.
- `ruleGated_heuristics_invariant` — what gating heuristic *birth* buys is
  an invariant over the heuristic population (a policy `P`), not
  soundness. The division of labor between the two gates is itself the
  theorem pair.

This is the **guarantee** axis: not "we check each proof" but "the
composition of all admissions, under any self-modification the proposers
attempt, preserves the invariant."

## 2. The gate, running — and its boundary

```
lake env lean Smoke.lean
```

The runtime gate (`Eureka/Runtime.lean`) realizes the model in `MetaM`:
statements are `Prop`-typed `Expr`s, evidence is a proof term, and
`commitFact` is a mechanical screen (no `sorry`, no metavariables,
statement is a `Prop`, proof type-checks) in front of the kernel
(`addDecl`), followed by an axiom audit.

The smoke test's second act is the important one. An adversarial heuristic
uses its full `MetaM` power to **mint an axiom** asserting `2 + 2 = 5` into
the environment, then proposes a "fact" proved from it. The proof genuinely
type-checks — screen and kernel both pass it — and it is the *axiom audit*
that refuses it:

```
evil admitted: []
evil rejected: [demo.evil]
```

The boundary, stated honestly: the heuristic's minted axiom persists in the
ambient environment (rollback removes only the refused theorem), but
nothing reaches the corpus without a clean audit — a later attempt to
launder a proof through the litter is refused too. The theorems protect the
corpus, not the environment, and not the filesystem (OS-level sandboxing of
metaprograms is out of scope, as in lean-sage's booth).

## 3. Proposers, first form: templates

```
lake env lean Disco.lean        # ~2 min
```

Six heuristics derive conjectures over `Nat` operations — identity,
commutativity, idempotence, associativity, distributivity templates, plus
`mixerH`, which reads the corpus and composes admitted facts. A
counterexample search refutes by evaluation; a prover ladder (refl,
grounding against the library, simp with the corpus, simp, omega) hunts for
evidence; the gate alone admits. Expect:

```
28 admitted (every one kernel-gated), 37 refuted, 0 open,
10 merged as definitional duplicates, 0 refused at the gate
```

Two things to notice, both **evidence kind** phenomena:

- *Grounding certificates*: most admissions read `grounded: Nat.gcd_comm` —
  the discovery is recognized as an alias of a library lemma, by a
  kernel-checkable proof, at admission time.
- *The synonym tower, priced out*: `∀ n, n - 0 = n` is merged into
  `∀ n, n + 0 = n` — definitionally the same proposition — before any
  proof effort is spent, and every merge is logged with its target.

`mixerH`'s generation-2 facts (proposed *from* admitted facts, proved by
simp *with* the corpus) are the loop feeding itself — discovery of
discoveries, still one gate.

## 4. Proposers, second form: the LLM behind the gate

```
lake env lean BoothStub.lean    # deterministic, no credentials
lake env lean BoothRun.lean     # live
```

The booth: the model sees the corpus and its previous round's outcomes and
proposes conjectures as bare Lean terms. Each line must survive parsing,
elaboration at `Prop`, dedup (verbatim and definitional), counterexample
search, the hunt, and the gate. The **proposer got smarter and the gate did
not get bigger** — that is the entire trust story of adding an LLM.

The stub exercises every path with a canned model. The live run's flavor:
the LLM proposes connective laws the templates cannot express
(`a - b + b = max a b`, grounded `Nat.sub_add_eq_max`), five true
conjectures outrun the tactic ladder and are honestly reported open, and
zero falsehoods survive.

## 5. The reflection move: the LLM writes the meta level

```
lake env lean ReflectStub.lean  # deterministic, no credentials
lake env lean ReflectRun.lean   # live
```

This is the **modification kind** axis at its EURISKO setting. The LLM
writes a *heuristic* — a Lean metaprogram of type
`Corpus → MetaM (Array Conjecture)` — and the system elaborates it, checks
the rule policy (interface type, no `sorry`, effect denylist: no
`IO.Process`, no `IO.FS`), compiles it through the interpreter, installs
it, and fires it.

The stub is the model's `admitRuleGated` executed literally, four
proposals in sequence:

1. a heuristic that spawns a process — **refused by policy**, before
   compilation;
2. a heuristic that doesn't elaborate — refused, with the error text fed
   back for retry (the proposer is in a feedback loop with the gate);
3. a working heuristic — installed; its discovery admitted with a
   grounding certificate;
4. a *well-typed junk* heuristic — **installed** (the rule gate checks
   policy, not taste), and every false conjecture it fires is refuted at
   the fact gate. `discovery_sound` says this had to be safe; here it is,
   running.

In the live run, round 1's LLM heuristic was a shotgun (~90 conjectures,
mostly false, refuted for pennies, 4 survivors admitted); the feedback said
*favor precision over volume*, and round 2's heuristic went 4 admitted of
5 proposed. The proposer's heuristic-*writing* improved across rounds while
the trusted base never moved.

## 6. Reflective depth: births, worth, death

```
lake env lean EvolveStub.lean   # deterministic, ~4 min
lake env lean EvolveRun.lean    # live
```

The **reflective depth** axis. Agents propose facts *or new heuristics as
source code*; births pass the rule gate; and the population runs an
economy: worth is earned (`admitRate × dupPenalty`, plus parent credit
paying heuristic-writers for their children's discoveries), a judge budget
is spent in worth order, and agents with enough trials and negligible
worth are killed.

Watch for the chain in the stub: `specializer` (a template meta-heuristic)
births `explore_min` through the rule gate, which births `probe_min`
through the rule gate, which discovers `min (min a a) b = min a b` through
the fact gate — a fact found by a heuristic written by a heuristic written
by a heuristic, every link certified. Meanwhile `junkH` is killed by the
kill rule after one generation.

In the live run the LLM joins as `llm_oracle`, one agent among many. Its
two children were shotguns and the kill rule executed both — the economics
judge the LLM's children by the same rules as everything else — while the
oracle itself ended at worth 1.00 via parent credit, tied with the
specializer atop the agenda.

Who gates the gate? Here the admission criteria are fixed; making them
reflectively modifiable through a gate one level up is
[lean-keep](https://github.com/namin/lean-keep)'s axis (`tower_safe`), and
the impossibility of unbounded self-trust in a replacement checker is
[lean-loeb](https://github.com/namin/lean-loeb)'s (`trust_forces_descent`).

## 7. Which EURISKO slots are gateable

The negative theory, from running the system rather than speculating:

| slot | evidence available | gateable? |
|---|---|---|
| fact admission (soundness) | proof term | fully — the kernel (`discovery_sound`) |
| vocabulary grounding (aliasing) | `iff`/defeq certificate | fully, in the alias direction |
| novelty | a *failed* alias search | semi: refutable, not certifiable |
| heuristic birth | elaboration, audit, policy | policy-gateable, not soundness-relevant (`ruleGated_heuristics_invariant`) |
| interestingness / worth | traces, statistics | **not proof-gateable** — its evidence is empirical, its gate is an economy |

The last row is why the population layer is an *economy* rather than a
prover: interestingness has no proof-shaped evidence, so its gate is
weaker by necessity, and the theorems are careful to promise nothing about
it.

## 8. Evidence beyond truth: grounding a synonym tower

*(needs `lake build EurekaMathlib`)*

```
lake env lean MatroidStub.lean  # ~3 min
```

The low-guidance instantiation: the user supplies one name — `Matroid` —
and the system extracts the namespace's predicates by signature shape (no
seed file, no curated canonical pool), certifies implication edges, and
probes *invented* predicates for aliases. The probes are the point: the
predecessor system (formal-disco-eurisko-verified) detected its matroid
synonym tower post-hoc at ~75s per subprocess probe; here the same
predicates certify in-process at admission:

```
✓ is_loop_def is Matroid.IsLoop (chained via Matroid.singleton_dep)
✓ dep_invented is Matroid.Dep (by unfold dep_invented Matroid.Dep; tauto)
```

`is_loop_def` is the literal invented predicate from that run's tower, and
its certificate is *composed*: a direct step to `M.Dep {e}` chained through
the library's own bridge with `Iff.trans`. Alias certificates are an
evidence kind of their own — kernel-checked claims about *vocabulary*, not
truth.

## 9. What it finds: the frontier harvest

```
lake env lean MatroidFrontierRun.lean  # ~10 min
```

The composition rung (bounded backward chaining, certificates naming every
lemma used) sweeps the exclusion family and yields **8 kernel-certified
facts not stated in Mathlib**, e.g. `M.Coindep X → ¬M.IsCocircuit X` —
composed from *circuit* lemmas, with unification silently instantiating the
matroid at `M✶`: the argument ran in the dual without any duality-aware
code. Full numbers and the baseline comparison: `REPORT_MATROID.md`.

## 10. Where the boundary honestly is

- The theorems guarantee corpus soundness and provenance — not
  termination (a looping heuristic hangs the loop), not OS effects
  (denylist is shallow; sandbox the process if you need more), not
  *interest* (see §7).
- No refuter exists for predicate domains yet: `open` conflates "false"
  with "hard". The economics findings in `REPORT_MATROID.md` (kill rule
  vs. enumeration order, three occurrences) are a direct consequence.
- Everything here operates on existing vocabulary. Concept *invention* —
  proposed definitions as a gated proposal kind with a grounding lifecycle
  at birth — is the open frontier, and the predecessor's
  `BRAINSTORM_ALIGN.md` is required reading before building it.

## Pointers

- `README.md` — the axes table, theorem list, roadmap.
- `REPORT_MATROID.md` — run data, numbers first.
- [reasonable-reflection](https://github.com/namin/reasonable-reflection)
  — the pattern and the sibling artifacts; this repo is its "verified
  discovery system" instance.
