# The record: transcripts, the benchmark, the cleanup

Not a capability arc — the maintenance arc the capability arcs earned:
the three debts whose interest is now visible. Decisions R1–R5,
acceptance tests fixed before code.

**Status: built.** R1: `Eureka.LLM.withTranscript` (JSONL per call,
`transcripts/` gitignored; capture test in `ProveStub.lean`, CI).
R3: one credit path (`creditAdmission`/`creditMerges` in
`Eureka/Evolve.lean`), the full 13-stub suite passing unchanged.
R4: `EvolveConfig.sweepBudget` wires the in-loop sweep; its
differentiating test — a pair whose enabling fact mentions neither
concept, structurally invisible to trigger (i) — passes in
`DepthStub.lean` (CI). R2: `BenchRun.lean`, corpus v1 pinned (16
matroid + 13 graph opens, sentinels, two-run determinism check) and
baselined — the deep symbolic ladder closes 1 of 29; REPORT_BENCH.md
holds the number to beat.

## The debts, named

- **Transcripts**: every live run's LLM exchange is lost — the Bedrock
  client overwrites two temp files per call. The baseline kept trace
  pickles; we cannot quote what the model said, compare run v1 to v2,
  or substantiate an n=1 claim like "zero restatements" beyond the
  fates the logs happened to print.
- **Measurement**: prover progress is anecdotes over hand-pinned
  corpora. The omega run's 83 opens and the matroid residuals are the
  natural standing benchmark, but they live nowhere.
- **Code health**: the admitted-fact bookkeeping (vocabulary credits,
  trigger (i), attracted credit) is copy-pasted three times in
  `Evolve.lean`; the sweep (D3-ii) was built in slice one and never
  wired into the loop; `evolveWith` has outgrown single-screen
  comprehension.

## Decisions

**R1 — Transcripts are a transport wrapper, not a client change.**
`Eureka.LLM.withTranscript (path : FilePath) (tag : String) (call)`
wraps any transport: each call appends one JSONL object
`{tag, i, prompt, response | error}` (index-ordered; no timestamps —
determinism rules). Every live run file wraps its transport;
`transcripts/` is gitignored. The canned stubs can wrap too, which is
what makes the acceptance test CI-able. Nothing changes for callers
that don't wrap.

**R2 — The benchmark is a frozen *generator*, not frozen statements.**
Statements mention `Invented.*` constants, so a text freeze would need
re-elaboration anyway; the runs are deterministic, so the corpus is
reproducible by construction. `BenchRun.lean` (Mathlib, deterministic,
not CI): regenerates the open sets from the pinned matroid and graph
configurations, **asserts the pin** (counts per family plus sentinel
statements present — drift is a loud corpus version bump, never
silent), then runs the symbolic ladders (cheap, deep) over the corpus
and prints the closure table. `REPORT_BENCH.md` records the numbers;
future prover work moves them or it didn't happen. LLM provers are
measured against the same corpus in live runs, reported separately.

**R3 — One credit path.** Extract the admitted-fact bookkeeping into a
single helper (`creditAdmission`: vocabulary credits to inventors,
trigger (i) re-probe, delayed-alias and attracted credits on merges,
the prints), called from all three sites (the fact branch, escalation,
repair). Behavior-preserving by test, not by claim: the full suite
must pass unchanged.

**R4 — The sweep joins the loop.** `EvolveConfig.sweepBudget : Nat := 0`
(off — every existing run unchanged): each generation, after
escalation, `sweepReprobe` runs with the budget and a cursor carried
across generations; its merges pay through the same credit path as
trigger (i). This closes the last unwired piece of DESIGN_INVENT D3 —
the standing-obligation tail that trigger (i) cannot reach (pairs whose
enabling fact mentions neither concept).

**R5 — Out of scope**, recorded for later: the whole-Mathlib alias
sweep that would quantify the novel-so-far honesty gap; price
sensitivity analysis; structured rung identity (the `tierOfRung`
string classifier); model-level counterparts for the ledger; agent
sandboxing. None of these blocks the three debts above.

## Acceptance tests (written before building)

1. **Transcripts capture** (`ProveStub.lean` extension, CI): a
   canned-transport exchange wrapped with `withTranscript` produces
   exactly N JSONL entries, prompts and responses intact, in call
   order; the file parses back.
2. **The benchmark pins and measures** (`BenchRun.lean`): the
   regenerated corpus matches the pinned counts and contains the
   sentinels; the cheap and deep ladders produce a closure table;
   `REPORT_BENCH.md` records the baseline.
3. **The refactor changes nothing** (the full CI suite, 13 stubs): all
   pass with no assertion edits; `GraphRun.lean` and
   `MatroidCompoundRun.lean` spot-check green.
4. **The sweep catches what trigger (i) cannot** (`DepthStub.lean`
   extension, CI): a stuck pair whose enabling fact mentions *neither*
   concept — trigger (i) is structurally blind to it — merges via the
   in-loop sweep once the fact lands, with delayed credit paid through
   the shared path.

## Sequence

1. R1 (+ test 1) — independent, smallest.
2. R3 + R4 (+ tests 3–4) — the refactor makes the sweep wiring clean.
3. R2 (+ test 2) — the benchmark runs on the refactored loop;
   `REPORT_BENCH.md`.
