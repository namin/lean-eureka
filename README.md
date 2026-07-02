# lean-eureka

_A verified discovery gate: EURISKO's reflection behind LCF's kernel._

EURISKO's defining move — heuristics that create heuristics — made it rich
and ungovernable: nothing checked what a heuristic put into the theory.
lean-eureka restores that full expressiveness and places a gate in front of
it. Heuristics are arbitrary untrusted code, including code that births new
heuristics; the only trusted component is the gate, and in the running system
the gate is the Lean kernel. The system may only say "eureka" when the kernel
agrees.

This is the "verified discovery system" instance of the
[reasonable-reflection](https://github.com/namin/reasonable-reflection)
pattern (substrate / gate / proposer).

## The model (`Eureka/Gate.lean`)

A small transition system: a `State` holds a corpus of statements and a
population of heuristics-as-code; a `Step` fires an installed heuristic under
an *adversarially chosen* interpreter and admits one of its proposals — a
fact with evidence, or a new heuristic. All theorems are axiom-free
(`Audit.lean` enforces this at build time).

| Theorem | Statement |
|---|---|
| `discovery_sound` | With the object gate alone — heuristic birth **unrestricted** — every state reachable from a sound seed has a sound corpus, for any adversarial heuristic code. |
| `discovery_provenance` | Everything in a reachable corpus is seed, or entered with gate-accepted evidence. |
| `UngatedCollapse.ungated_reaches_unsound` | Remove the gate (Lenat's regime) and one firing of a malicious heuristic corrupts the corpus. |
| `UngatedCollapse.gated_immune` | The same seed, same malicious interpreter, behind the gate: no reachable state is unsound. |
| `ruleGated_heuristics_invariant` | Gating heuristic *birth* buys policy invariants over the heuristic population — not soundness, which the object gate already secured. |

The pair (`discovery_sound`, `ruleGated_heuristics_invariant`) is the
division of labor: kernel-checking facts is what soundness needs; checking
heuristics is about *governance* of the population (resource discipline,
non-duplication), a strictly separate concern.

## The runtime (`Eureka/Runtime.lean`)

The model realized in Lean metaprogramming: statements are `Prop`-typed
`Expr`s, evidence is a proof term, the gate is `commitFact` — a mechanical
screen (no `sorry`, no metavariables, no loose fvars, statement is a `Prop`,
proof type-checks against it) in front of the kernel (`addDecl`), followed by
an axiom audit (`propext`, `Classical.choice`, `Quot.sound` only). Refusal
leaves the environment unchanged. A `Heuristic` is arbitrary metaprogram
code; the LCF discipline — `Fact` in the role of `thm` — means nothing it
returns reaches the corpus except through the gate.

`Smoke.lean` exercises it, including adversarially: a heuristic proposes an
honest fact, a false fact with a type-incorrect proof, and a `sorry`-backed
fact — the gate admits exactly the first. A second heuristic uses its full
`MetaM` power to mint an axiom asserting a falsehood and proposes a "fact"
proved from it; the proof genuinely type-checks, so the screen and the kernel
both pass it, and it is the axiom audit that refuses it. The boundary of the
guarantee is exactly the model's: a heuristic can litter the ambient
environment (its minted axiom persists after rollback), but nothing reaches
the corpus without a clean audit — a later attempt to launder a proof through
the litter is refused at admission.

## The discovery loop (`Eureka/Prover.lean`, `Eureka/Heuristics.lean`, `Eureka/Loop.lean`)

`Disco.lean` runs generations of: heuristics propose conjectures *derived*
from templates and from the corpus (nothing hardcoded), a counterexample
search refutes by evaluation, a prover ladder hunts for evidence (`refl`,
grounding against the `Nat.*` library — direct and symmetric — then simp
with the corpus itself, then the default simp set, then `omega`), and the
gate alone admits. On the `Nat` algebra demo (7 operations, 5 law templates plus a
corpus-reading mixer):

```
28 admitted (every one kernel-gated), 37 refuted, 0 open,
10 merged as definitional duplicates, 0 refused at the gate
```

Three behaviors worth noticing in the output:

- **Grounding certificates.** Most admitted facts arrive as
  `grounded: Nat.gcd_comm` — the discovery is recognized as an alias of a
  library lemma, by a kernel-checkable proof, at admission time.
- **The synonym tower, caught at proposal time.** `∀ n, n - 0 = n` is merged
  into `∀ n, n + 0 = n` — they are *definitionally the same proposition* —
  before any proof effort is spent. Ten such merges in the demo run, each
  logged with its target, none silent.
- **Second-generation discovery.** The mixer's conjectures are built from
  gen-1 admitted facts, and the survivors are proved by simp *using the
  corpus* — discoveries proposing and proving discoveries.

The prover and heuristics are untrusted by construction; a hunt that
returned garbage evidence would be refused at the gate (`refused` counts it,
and the count is zero only because the rungs are honest).

## The booth (`Eureka/Booth.lean`, `Eureka/LLM.lean`)

Stage one of the LLM proposer: the model (Claude on Bedrock, client ported
from lean-sage) sees the corpus and its previous round's outcomes and
proposes conjectures as bare Lean terms. Each line must survive parsing,
elaboration at `Prop`, verbatim and definitional dedup, counterexample
search, the evidence hunt, and the gate — the LLM is a proposer exactly like
the template heuristics, smarter and no more trusted. The transport is a
parameter, so `BoothStub.lean` exercises every path deterministically
(CI-able, no credentials) while `BoothRun.lean` runs live.

A live 3-round run on top of the template corpus admitted 16 LLM-proposed
facts (every one kernel-gated), including connective laws the templates
cannot express — `∀ a b, a - b + b = max a b` (grounded: `Nat.sub_add_eq_max`),
`∀ a b, a.gcd (a + b) = a.gcd b` (grounded: `Nat.gcd_self_add_right`),
`∀ a b c, a ^ (b + c) = a ^ b * a ^ c` (grounded: `Nat.pow_add`) — plus two
facts admitted by simp with no library alias. Five true-but-unproved
conjectures were honestly reported open (`min a b + max a b = a + b`,
`a² - b² = (a-b)(a+b)`, …): the proposer already outruns the tactic ladder,
which is the depth ceiling made visible. (The `omega` rung, added since,
proves the linear four; the nonlinear `min a b * max a b = a * b` still
stands open — the ceiling moves, honestly, one rung at a time.) Two proposals were merged as
definitional duplicates of corpus facts. Zero falsehoods survived to the
corpus; zero garbage evidence reached it (`refused = 0`).

## Stage two: heuristics as code (`Eureka/Reflect.lean`)

The runtime analogue of the model's `.rule` proposals, and the artifact's
headline made live: the LLM writes a *heuristic* — a Lean metaprogram of
type `Corpus → MetaM (Array Conjecture)` — which is elaborated, checked
against the rule policy (interface type, no `sorry`, effect denylist: no
`IO.Process`/`IO.FS`), compiled through the interpreter, installed, and
fired. Rejections feed the error text back for a retry, lean-sage style.
Everything a born heuristic proposes still passes the fact gate; per
`discovery_sound` the rule gate was never needed for corpus soundness, and
per `ruleGated_heuristics_invariant` what it buys is policy over the
heuristic population — the model's division of labor, executed.

`ReflectStub.lean` drives the gate deterministically: a heuristic that
spawns a process (refused: policy), a heuristic that doesn't elaborate
(refused: error fed back), a working one (installed; its discovery admitted
with a grounding certificate), and a well-typed junk heuristic (installed —
the rule gate checks policy, not taste — with every false conjecture it
fires refuted at the fact gate).

In the live run, round 1 produced a shotgun: a well-typed schema enumerator
whose ~90 conjectures were mostly false — refuted for pennies — with 4
survivors admitted, including the absorption laws `max a (a - b) = a`,
`min a (a + b) = a`, and `a.gcd (a * b) = a`. The round feedback said
*favor precision over volume*; round 2's heuristic (a targeted gcd-addition
family) went 4 admitted of 5 proposed. The proposer's heuristic-writing
improved across rounds while the trusted base did not move.

## The population (`Eureka/Evolve.lean`)

The EURISKO layer. Template and born heuristics live in one population as
`Agent`s; any agent may propose facts *or new heuristics as source code*
(`RProposal.rule`), so heuristics birth heuristics to any depth — births
pass the rule gate, facts pass the fact gate, exactly the model's
`admitRuleGated`. Worth is earned, not declared:

    worth = min 1 (admitRate × dupPenalty)

with a duplication penalty that prices in the synonym tower (the
worth-credits-duplicators bias observed in formal-disco-eurisko-verified is
unprofitable here by construction) and parent credit that pays
heuristic-writers for their children's discoveries. Each generation spends
a judge budget in worth order — low-worth agents starve — and agents with
enough trials and negligible worth are killed.

`EvolveStub.lean` (deterministic, no LLM): the agenda visibly reorders on
worth; `junkH` is killed after one generation; the `specializerH`
meta-heuristic births an explorer per operation (heuristic code generated
from corpus data), and each explorer births a probe — reflective depth 2,
with facts like `min a (min a b) = min a b` (grounded: `Nat.min_self_assoc`)
discovered by a heuristic written by a heuristic written by a heuristic.

`EvolveRun.lean` (live): the LLM joins the population as `llm_oracle`, an
agent whose only move is to birth heuristics. In the live run its two
children were shotguns and the kill rule executed both (worth 0.03 and 0.02
after ~15 and 25 refutations) — while the oracle itself ended at worth 1.00
via parent credit for its child's one grounded discovery, tied with the
specializer at the top of the agenda. The economics judge the LLM's
children by the same rules as everything else.

## Mathlib domains (`EurekaMathlib/Domain.lean`)

The low-guidance move, first slice. The user supplies one name — `Matroid` —
and the system extracts the namespace's predicates from the environment by
signature shape (9 found: `Indep`, `Dep`, `IsBase`, `IsCircuit`, …; no seed
file, no curated canonical pool), maps their implication structure, and
probes invented predicates for certified aliases. `MatroidStub.lean` runs
it on the synonym tower's own examples from the formal-disco matroid run:

- **Implication edges, kernel-certified**: `IsBase → Indep` (grounded:
  `Matroid.IsBase.indep`), `IsCircuit → Dep` (grounded:
  `Matroid.IsCircuit.dep`); 42 candidate implications honestly open — there
  is no counterexample search in this domain, so non-theorems land in
  `open`, not `refuted`.
- **Alias probes, in-process**: `dep_invented` (Matroid.Dep with the
  conjuncts swapped — not defeq) is certified `↔ Matroid.Dep` by an
  unfold-then-`tauto` rung. This is the probe that cost ~75s per candidate
  as a subprocess in the Python system (BRAINSTORM_ALIGN facet 1.B), now a
  `MetaM` call against the already-loaded environment.
- **Transitive grounding**: `is_loop_def` (the run's literal invented loop
  predicate) is certified `↔ Matroid.IsLoop` by *composing* certificates —
  a direct step `is_loop_def ↔ M.Dep {e}` (unfold + aesop) chained through
  the library bridge `Matroid.singleton_dep : M.Dep {e} ↔ M.IsLoop e` with
  `Iff.trans` (`tryKnownChain` in the core prover, one step deep and
  domain-agnostic). The certificate names the bridging lemma.

The `Eureka` core library remains Mathlib-free — `lake build` is 12 jobs;
the domain layer is a separate `EurekaMathlib` target, and `MatroidStub` is
not in CI.

## Keynote axes

| Axis | Instance |
|---|---|
| Substrate kind | a heuristic agenda over a growing corpus of statements |
| Modification kind | admitting a fact; installing (or birthing) a heuristic |
| Evidence kind | a kernel-checked proof term (facts); elaboration + audit (code) |
| Policy | proof type-checks, axiom footprint bounded; code passes policy `P` |
| Guarantee | every reachable corpus is sound and gate-provenanced |
| Reflective depth | heuristics birth heuristics, unrestricted; gating the gate is `lean-keep`'s axis, its Löbian limit is `lean-loeb`'s |

## Which EURISKO slots are gateable

| Slot | Evidence available | Gate |
|---|---|---|
| fact admission (soundness) | proof term | kernel — fully gateable (`discovery_sound`) |
| concept grounding (aliasing) | `iff`/defeq certificate | kernel — fully gateable, one direction |
| novelty | a *failed* alias search | semi: refutable, not certifiable |
| heuristic birth | elaboration, audit, policy `P` | policy-gateable (`ruleGated_heuristics_invariant`), not soundness-relevant |
| interestingness / worth | traces, statistics | not proof-gateable; evidence is empirical |

## Building

```
lake build                    # library + model theorems
lake env lean Audit.lean      # axiom audit (all headline theorems axiom-free)
lake env lean Smoke.lean      # runtime gate smoke test (incl. adversarial round)
lake env lean Disco.lean      # the discovery run
lake env lean BoothStub.lean  # booth pipeline test, deterministic, no credentials
lake env lean BoothRun.lean   # live: discover, then 3 LLM conjecture rounds (needs aws CLI + Bedrock)
lake env lean ReflectStub.lean # rule-gate test, deterministic, no credentials
lake env lean ReflectRun.lean  # live: the LLM writes heuristic code, gated and fired
lake env lean EvolveStub.lean  # population engine: worth, budget, kill rule, depth-2 births
lake env lean EvolveRun.lean   # live: the LLM as one agent in the population
lake build EurekaMathlib && lake env lean MatroidStub.lean  # matroid microcosm (Mathlib)
```

Toolchain: `leanprover/lean4:v4.30.0`. The `Eureka` core has no
dependencies; the `EurekaMathlib` domain layer requires Mathlib.

## Neighbors

- [LeanDisco](https://github.com/namin/LeanDisco) — the pre-gate design
  (discovery loop in `MetaM`, symbolic proposer); kept frozen as baseline.
- formal-disco `eurisko-verified` branch — the Python/subprocess predecessor;
  its findings (synonym tower, priority starvation, depth ceiling) motivate
  this design; its matroid run is the comparison baseline.
- [lean-sage](https://github.com/namin/lean-sage) — the LLM-proposer /
  kernel-gate machinery (`booth`) to be reused here for LLM-proposed
  heuristics.
- [lean-keep](https://github.com/namin/lean-keep) /
  [lean-loeb](https://github.com/namin/lean-loeb) — who gates the gate, and
  the Löbian limit.

## Roadmap

- [x] Gate model with soundness, provenance, collapse, and policy theorems
- [x] Runtime gate: screen + kernel + axiom audit; heuristic firing
- [x] Discovery loop: generative + corpus-reading heuristics, counterexample
      search, prover ladder, generational driver to fixpoint
- [x] Grounding, first slice: definitional-alias merging at proposal time and
      library grounding certificates (direct and symmetric) at proof time
- [x] Grounding probes beyond defeq: certified `iff` alias probes with an
      unfold/`tauto`/`aesop` ladder (`aliasProbe`); `=`/`↔`/implication keys
      and universe-polymorphic lemmas in the grounding pool
- [x] Mathlib domains, first slice: predicates extracted from a namespace by
      signature shape, implication sweep with certified edges, alias probes
      on the actual synonym-tower examples (`MatroidStub.lean`)
- [x] Transitive alias chaining: `tryKnownChain` composes a provable step
      with a known library `iff` via `Iff.trans` — closes
      `is_loop_def ↔ Dep {e} ↔ IsLoop` through `Matroid.singleton_dep`
- [ ] Deeper chains (search the iff graph, not one step); alias chaining for
      `=`-shaped grounding via `Eq.trans`
- [ ] Matroid discovery proper: templates/LLM booth over the extracted
      predicates; comparison against the formal-disco matroid baselines
- [x] LLM-proposed facts through the gate (booth stage one; Bedrock client
      ported from lean-sage)
- [x] LLM-proposed *heuristic code*, elaborated, policy-checked, compiled,
      installed, and fired (booth stage two — the reflection move; see
      `ReflectRun.lean`)
- [x] Born heuristics as persistent citizens: one population of agents,
      multiplicative worth with duplication penalty and parent credit,
      budget-by-worth, kill rule, births to depth ≥ 2 (`Eureka/Evolve.lean`)
- [x] `omega` rung via generic by-tactic elaboration (`tryTacticRung`) —
      closes the linear opens from the live runs
- [ ] Further prover rungs (induction templates, nonlinear arithmetic) —
      `min a b * max a b = a * b` is the standing open
- [ ] Worth/agenda layer; reflective worth modification behind the gate
- [ ] Matroid microcosm; comparison against the formal-disco baselines
