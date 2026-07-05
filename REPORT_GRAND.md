# REPORT: compounding and the grand run (lean-eureka)

Slice two of concept invention (DESIGN_INVENT C1–C5) and the first
full-population run: every agent kind the system has — template fact
agents, generative operators, the compounder, the invented-implications
agent, the LLM concept booth — in one `evolve` population under the
repriced economy, the invented-aware refuter, and re-probe trigger (i).
Every "certified" below is a kernel-gated fact.

## Setup

- Compounding (C1–C3): `compounderAgent` reads the live pool via
  `Agent.proposeP` and re-applies dualization and singleton-lift to
  invented survivors; depth recorded on every concept, capped at 2;
  boolean operators do not re-enter.
- C4: alias credit decays per agent (on top of per-target zeroing) —
  mechanical alias-mining declines with scale.
- The booth as an agent (`conceptBoothAgent`): one LLM round per
  firing, the pool as its feedback.
- Grand run config: 8 agents, 4 generations, judge budget 40, probe
  budget 5000, alias-only births, invented-target window 12; refuter
  `unfold`-prefixed for invented vocabulary; Claude (Sonnet, Bedrock),
  one call per generation while the booth lives.

## Run A — compounding, deterministic (`MatroidCompoundRun.lean`, S1–S3)

Dualizer (depth 1) + compounder (depth 2), three generations. The
depth-2 pool: `dual_dual_Dep ≡ Dep`, `dual_dual_IsBase ≡ IsBase`,
`dual_dual_IsRkFinite ≡ IsRkFinite` (the duality involution as
certified merges), `elem_dual_Dep ≡ IsColoop` (a genuine composed
bridge: `M✶.Dep {e} ↔ M.IsColoop e`), `elem_dual_IsRkFinite ≡ ⊤`
(caught degenerate), `elem_dual_IsBase` the honest depth-2 novel. Depth
cap held; C4's decay bit (alias pay 2.71 vs 3.25 undecayed).

The recorded lesson: the first S1 assertion demanded the compounder
rank below the dualizer, and *correctly failed* — the compounder's
certified rate is higher (5/6 vs 6/9) and its lifts are real bridges.
The decay is a long-run cap on mining, not a small-n ordering; the memo
now says so.

## Run B — the grand run (`MatroidGrandRun.lean`, S4)

Four generations, ~24 minutes, elaboration clean on first contact,
audit clean, all assertions passed. 45 concepts born (21 at depth 1,
24 at depth 2), corpus 81 certified facts, 16 of them in invented
vocabulary. Three LLM calls — see the booth's fate below.

**The headline: certified duality theorems over LLM vocabulary.** The
booth invented `MatroidIsSimplePoint` and `MatroidIsSeriesPoint`
(generation 1) and `MatroidIsCircuitCore` / `MatroidIsCocircuitCore`
(generation 3). The compounder dualized them, and the identity probe
certified the products against the *other LLM inventions*:

```
dual_MatroidIsSimplePoint  ≡ MatroidIsSeriesPoint
dual_MatroidIsSeriesPoint  ≡ MatroidIsSimplePoint
dual_MatroidIsCircuitCore  ≡ MatroidIsCocircuitCore
dual_MatroidIsCocircuitCore ≡ MatroidIsCircuitCore
```

Four kernel-checked bridges stating that the model's concept pairs are
duals of each other — structure *about* invented vocabulary, discovered
by mechanical composition, certified by the kernel, with none of the
four predicates in Mathlib. This is the first genuinely new certified
structure over genuinely new vocabulary the system has produced: the
"does invention pay for itself" question has its first positive
datapoint.

**Yield did not decay at depth 2.** Depth 1: 6 certified / 21 (29%);
depth 2: 9 certified / 24 (38%). Compounding structure-aware operators
over structured inputs *beat* the depth-1 rate — the opposite of the
AM expectation, at admittedly small n, and exactly the configuration
C1 chose (the boolean operators, which would have dragged the rate
down, were excluded by rule).

**The economy's verdicts.** Final standings: exclusions 0.46 (6
admitted + 13 certified refutations), singleton 0.39, dualizer 0.38,
duality 0.29, compounder 0.21, implications 0.19. Killed:
`invented_impls` (worth 0.03 — 33 of its 34 conjectures landed open;
the prover's depth ceiling on invented-vocabulary implications, live)
and — the notable one — **`concept_booth` (worth 0.04, killed in
generation 3)**: twelve inventions, all novel-so-far, all worth zero
under pay-certainty pricing. Its concepts then earned four certified
bridges in generation 4, *after its death*, with the credit flowing to
the compounder (the prober), not the inventor.

## Interpretation (separate from the facts above)

1. **The integrated system works.** Eight agent kinds, three proposal
   kinds, two LLM roles, the refuter, trigger (i), and the economy ran
   together for four generations with a clean audit and no crash — and
   produced its best single result (the LLM-vocabulary duality
   bridges) precisely from the *interaction* of parts: booth invents,
   compounder composes, probe certifies, none sufficient alone.
2. **The booth's death is the Arc 3 problem, live and quantified.**
   Pay-certainty pricing is correct against noise-farming (the derby)
   but cannot distinguish a slow deep invention from noise until it
   earns — and here the earning arrived one generation after the kill,
   paid to the wrong agent. Two concrete gaps for Arc 3: posthumous /
   attracted-structure credit (a bridge *about* your concept should pay
   you even when another agent's probe found it — today the
   `inventedEdge` credit fires only on judged facts, not on
   concept-path bridges), and some priced form of promise (the
   baseline's difficulty term).
3. **The depth ceiling is now the binding constraint.**
   `invented_impls` died honestly: implications over LLM concepts with
   closure-heavy bodies are beyond tauto/omega/targeted-simp at these
   budgets. The interesting conjectures exist and are being proposed;
   they land open. A deeper prover (induction, closure lemmas, bigger
   aesop budgets on selected candidates) is where the next real
   discovery capacity is.

## Reproduction

```
lake env lean MatroidCompoundRun.lean  # S1–S3 (Mathlib, deterministic)
lake env lean MatroidGrandRun.lean     # S4 (Mathlib + Bedrock, ~25 min)
```
