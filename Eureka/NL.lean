import Eureka.Booth

/-!
# Natural-language heuristics (DESIGN_HEURISTICS_NL)

The third heuristic representation: the body is an English string,
interpreted by an LLM at every firing. The body is DATA — never
elaborated, compiled, or executed. A trusted combinator (`nlAgent`,
`Eureka/Evolve.lean`) splices it into a stage-one-booth prompt, and the
replies go through the booth pipeline — parse at `Prop`, dedup, judge,
gate — like any other facts.

The NL birth gate here (`nlBodyCheck`) is mechanical policy, not
soundness — the analogue, for a representation that cannot execute, of
the rule gate's effect denylist: minimum body length and token-Jaccard
dedup against live bodies (both from the lean-eurisko baseline's
soundness gate). Soundness never depended on it: `discovery_sound`
quantifies over arbitrary adversarial interpreters, and an LLM
interpreting English is one instantiation. What replaces the denylist's
question ("what may this code reach?") is metering — the loop spends
`nlProposeBudget` per generation and prices each call as `.llmCalled`
attention (N4), expense the economy can see.
-/

open Lean Meta

namespace Eureka
namespace Runtime

/-- N2: minimum body length, from the baseline's soundness gate. -/
def nlMinBodyLength : Nat := 30

/-- N2: token-Jaccard similarity at or above which a proposed body is a
duplicate of a live one. -/
def nlDupThreshold : Float := 0.7

/-- Lowercased alphanumeric tokens, deduplicated. -/
def nlTokens (s : String) : Array String := Id.run do
  let mut out : Array String := #[]
  for w in s.toLower.split (fun c => !Char.isAlphanum c) do
    let w := w.toString
    if !w.isEmpty && !out.contains w then
      out := out.push w
  return out

/-- Token Jaccard similarity of two bodies. -/
def nlJaccard (a b : String) : Float :=
  let ta := nlTokens a
  let tb := nlTokens b
  let inter := (ta.filter tb.contains).size
  let union := ta.size + tb.size - inter
  if union == 0 then 1.0 else inter.toFloat / union.toFloat

/-- The NL birth gate (N2): `none` = clean, `some msg` = refusal.
Mechanical checks over data; buys the population invariant "no vacuous
or duplicate NL heuristics", never soundness. -/
def nlBodyCheck (body : String) (live : Array String) : Option String :=
  if body.trimAscii.toString.length < nlMinBodyLength then
    some s!"body shorter than {nlMinBodyLength} characters"
  else if live.any (fun b => nlJaccard body b ≥ nlDupThreshold) then
    some "duplicate of a live NL heuristic (token Jaccard above threshold)"
  else
    none

/-- Conjectures requested per firing. -/
def nlPerFiring : Nat := 6

/-- The firing prompt (N1/N3): the body under a `## Heuristic to apply`
header (the baseline's interpolation point), the corpus, feedback on the
previous firing's unparseable lines, and the stage-one output format.
The reply goes through `extractCandidates`/`parseConjecture` — the booth
pipeline, unchanged. -/
def renderNLPrompt (body : String) (corpus : Corpus)
    (feedback : Option String) (perFiring : Nat := nlPerFiring) :
    MetaM String := do
  let mut facts := ""
  for f in corpus.facts do
    facts := facts ++ s!"  {toString (← ppExpr f.stmt)}\n"
  let fb := match feedback with
    | some s => s!"\nUnparseable lines from your previous firing \
(follow the output format exactly):\n{s}\n"
    | none => ""
  return s!"You are one heuristic inside a verified mathematical discovery \
system. Your proposals are machine-checked: tested on small cases, then \
proof-searched, then admitted by the Lean kernel or rejected. False or \
duplicate conjectures are wasted effort.

## Heuristic to apply
{body}

Established corpus (Nat = natural numbers, so subtraction is truncated):
{facts}{fb}
Apply the heuristic above to propose up to {perFiring} NEW conjectures about \
the operations +, *, -, ^, max, min, Nat.gcd on Nat that are plausibly TRUE \
for ALL natural numbers and are not already in the corpus.

Output format — exactly one conjecture per line, as a bare Lean 4 term, \
nothing else:
∀ (a b : Nat), <lhs> = <rhs>
No prose, no numbering, no code fences."

/-- The NL oracle's prompt (N5): ask for a new heuristic *as English*.
The oracle cannot see the live bodies (agents see only the corpus), so
duplicate births are possible — the NL gate refuses them and the refusal
is priced; the economy, not the prompt, is the dedup backstop. -/
def renderNLOraclePrompt (corpus : Corpus) : MetaM String := do
  let mut facts := ""
  for f in corpus.facts do
    facts := facts ++ s!"  {toString (← ppExpr f.stmt)}\n"
  return s!"You are proposing a new discovery HEURISTIC for a verified \
mathematical discovery system — as ENGLISH INSTRUCTIONS, not code and not \
conjectures. At every firing, the heuristic's text is shown to an LLM \
together with the current corpus, and the LLM applies it to propose \
conjectures about the Nat operations +, *, -, ^, max, min, gcd, which are \
then machine-tested and kernel-checked.

Established corpus:
{facts}
Write ONE new heuristic: 2-8 lines of English instructions describing a \
family of conjectures worth looking for that the corpus does not cover \
yet. Output the instructions only — no title, no commentary, no code."

/-!
## Seed bodies (N5)

Verbatim ports of the baseline's conjecture-kind templates
(`lean-eurisko/discovery/heuristics_seed.py`), minus each template's
output-format line ("Express each ... as a Lean 4 theorem statement"),
which conflicts with the booth's bare-`∀` line format — the renderer
owns the format (N3).
-/

def nlSeedAlgebraicIdentities : String :=
"Conjecture ALGEBRAIC IDENTITIES involving the given concept(s).
Look for laws such as:
  - Involution: f(f(x)) = x
  - Idempotence: f(f(x)) = f(x)
  - Commutativity: f(x, y) = f(y, x)
  - Associativity: f(f(x, y), z) = f(x, f(y, z))
  - Absorption: f(x, g(x, y)) = x
  - Distributivity: f(x, g(y, z)) = g(f(x, y), f(x, z))
  - Cancellation: f(x, y) = f(x, z) -> y = z"

def nlSeedBoundaryCases : String :=
"Explore BOUNDARY CASES and edge cases of the given concept(s).
Consider:
  - Identity element: what happens at e / 1 / 0?
  - Inverse: what happens at x⁻¹?
  - Equal arguments: f(x, x)
  - Trivial structures: the trivial group, empty set, zero ring
  - Extreme values: n = 0, n = 1, singleton sets
  - Self-application: applying an operation to itself"

def nlSeedAnalogyTransfer : String :=
"TRANSFER the given theorem(s) to analogous structures by analogy.
Analogies to consider:
  - Group <-> Ring <-> Module
  - Nat <-> Int <-> Rat <-> Real
  - List <-> Multiset <-> Finset
  - Monoid <-> Group (what happens without inverses?)
  - Additive <-> Multiplicative notation"

/-- The seed rung for the representation derby (N6). -/
def nlSeeds : List (Name × String) :=
  [(`nl_algebraic_identities, nlSeedAlgebraicIdentities),
   (`nl_boundary_cases, nlSeedBoundaryCases),
   (`nl_analogy_transfer, nlSeedAnalogyTransfer)]

end Runtime
end Eureka
