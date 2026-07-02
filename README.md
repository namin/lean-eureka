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
lake build            # library + model theorems
lake env lean Audit.lean   # axiom audit (all headline theorems axiom-free)
lake env lean Smoke.lean   # runtime gate smoke test
```

Toolchain: `leanprover/lean4:v4.30.0`, no dependencies.

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
- [ ] Corpus-aware heuristics: propose from admitted facts and the ambient
      environment (Mathlib namespace as seed — no hand-written seed files)
- [ ] Grounding probes: in-process defeq/`iff` alias certificates at
      admission time (the synonym-tower fix)
- [ ] LLM-proposed facts, then LLM-proposed *heuristic code*, admitted
      through the gate (lean-sage booth pattern)
- [ ] Worth/agenda layer; reflective worth modification behind the gate
- [ ] Matroid microcosm; comparison against the formal-disco baselines
