# DESIGN_MATERIALIZE — a corpus library as a sibling Lake project

## Goal

A run currently ends by printing its corpus and exiting; the kernel-checked
facts die with the process. Materialize them instead: at the end of a run,
write the admitted concepts and facts as Lean source into a sibling Lake
project, `../eureka-corpus`, which builds against the same toolchain and
Mathlib. The sibling is the cumulative, independently checkable library of
everything the system has discovered — the analogue of what formal-disco
(`lean-eurisko` branch) does with `../LeanDisco` via
`proof_worker._write_to_library`.

The formal-disco precedent is deliberately minimal — write the proved file
into `LeanDisco/Domains/<Domain>/<Name>.lean`, cumulative, success-only —
and this design copies that minimalism. The one problem it has that
formal-disco doesn't: formal-disco verifies the *exact file text* it stores
(the proof is a subprocess-checked `.lean` file already), whereas
lean-eureka's facts are in-memory `Expr`s checked by the in-process kernel.
Materialization must render `Expr`s back to source, and rendered source is a
*new* artifact that has not been checked. So the design has exactly one
non-obvious component: a round-trip check at emission time, with the sibling's
`lake build` as the end-to-end gate.

## Non-goals (v1)

- No feedback loop: future runs do not import the sibling library. (That is
  formal-disco's step 4; here it is future work.)
- No cross-run deduplication or merging: runs land in separate namespaces
  and the library is cumulative, like LeanDisco ("nothing is removed once
  added").
- No proof re-search at materialization time: a fact that fails to render is
  quarantined and reported, not re-proved.
- No database, no JSON sidecars, no per-fact files.

## The sibling project

```
../eureka-corpus/
  lakefile.toml            -- requires mathlib, same lean-toolchain as here
  lean-toolchain
  EurekaCorpus.lean        -- imports the domain aggregators
  EurekaCorpus/
    Matroid.lean           -- imports EurekaCorpus.Matroid.*
    Matroid/
      GrandRun_2026_07_20.lean   -- one file per materialized run
    Graph.lean
    Graph/…
    Nat.lean
    Nat/…
  Audit.lean               -- axiom audit over everything materialized
  README.md
```

One file per **run**, not per fact. formal-disco writes one file per theorem
because each of its proofs is self-contained; here a run's facts share the
run's invented `Invented.*` concepts, so the run is the natural
self-contained unit. Within the file, everything lives in a per-run
namespace (`EurekaCorpus.Matroid.GrandRun_2026_07_20`), so re-runs and
overlapping discoveries across runs can never clash — dedup is deferred by
construction, not by care.

## What a run file contains

Header comment: source repo + commit, driver file, date, counts
(admitted / materialized / quarantined). Then, inside the run namespace:

1. **Concepts first**, in birth order (which is dependency order — a
   concept can only mention earlier-born concepts): each live pool concept
   whose definition some materialized fact mentions, emitted as
   `def Invented.<name> : <type> := <value>` by delaboration. Inside the run
   namespace the relative name `Invented.<name>` resolves correctly, so
   statements that mention invented predicates render unchanged. Tombstoned
   (merged) concepts are emitted only if a materialized fact still mentions
   them, with their `mergedInto` target noted in the doc comment.
2. **Facts**, in admission order: each corpus fact as

   ```lean
   /-- origin: llm_booth (round 2); rung: grounded (Matroid.IsBase.compl_isBase_dual) -/
   theorem isBase_compl_dual : ∀ …  := <delaborated proof term>
   ```

   The doc comment is provenance: origin agent, proving rung, grounding
   certificate when there is one. The proof is the delaborated
   kernel-accepted proof term — for most facts this is tiny (`Nat.gcd_comm`,
   `fun a b => …`), because grounding certificates *are* small terms.

3. **A quarantine block** at the bottom: facts whose statement or proof did
   not survive the round-trip check, as comments (statement text plus
   certificate note) — never as `sorry`-backed declarations. The library
   contains only what builds; the quarantine keeps the failure honest and
   countable, in the same spirit as `refused`/`open` in the run output.

## Rendering and the round-trip check

`Eureka/Materialize.lean` (core layer, imports only Lean — like `Runtime`):

- **Render**: delaborate `stmt` and `proof` with `pp.fullNames := true`.
  If elaborating the rendered pair back in the current environment fails to
  produce something defeq-typed against the original `stmt`, retry with
  `pp.explicit := true`; if that also fails, quarantine the fact. This check
  runs in the same `MetaM` as the run (environment already loaded, so it
  costs a re-elaboration, not a subprocess — the same economy argument as
  the alias probes).
- The in-process check is an approximation (the sibling file namespaces the
  names and imports Mathlib afresh); the authority is `lake build` in the
  sibling. A materialized file that fails there is a bug in the renderer,
  surfaced loudly, not silently absorbed.
- **Write**: `IO.FS.writeFile` the run file; append the run's `import` line
  to the domain aggregator and the domain's line to `EurekaCorpus.lean` if
  missing (mechanical, idempotent). Refuse to overwrite an existing run file
  — the run id (driver name + date, supplied by the driver) makes each
  materialization a fresh file, matching the cumulative-only rule.

API, roughly:

```lean
structure MatCfg where
  dir     : System.FilePath      -- ../eureka-corpus, from EUREKA_CORPUS_DIR
  domain  : String               -- "Matroid"
  runId   : String               -- "GrandRun_2026_07_20"
  header  : String               -- provenance text

def materialize (cfg : MatCfg) (pool : ConceptPool) (corpus : Corpus) :
    MetaM MatReport   -- counts: written, quarantined (with reasons)
```

## Provenance on `Fact`

The renderer wants `origin`, `rung`, and `knownAs` for the doc comments.
Today `Verdict.proved` carries `rung`/`knownAs` and the conjecture carries
`origin`, but `commitFact` drops them. Add three metadata fields to
`FactProposal`/`Fact` (`origin : Name`, `rung : String`,
`knownAs : Option Name`, all defaulted) and thread them through where
`judge` builds the proposal. Metadata only — the gate's checks are
untouched, so this does not move the trusted base.

## Verification in the sibling

- `lake build` builds every materialized run file — the same standard
  formal-disco applies ("runs `lake build` to verify the file integrates
  cleanly"), and the real check that rendering round-tripped.
- `Audit.lean` mirrors this repo's `Audit.lean`: walk every theorem under
  `EurekaCorpus.*`, `collectAxioms`, refuse anything outside
  `propext / Classical.choice / Quot.sound`. The gate audited each fact at
  admission; the sibling re-audits the *rendered* artifact, so the library's
  guarantee is its own, not inherited by trust in the renderer.

Both run in the sibling's CI. lean-eureka's CI is unchanged (materialization
of Mathlib-domain runs isn't in CI, same as the live runs themselves), except
that a stub (`MaterializeStub.lean`) exercises render/round-trip/quarantine
deterministically on the `Nat` corpus, writing to a temp dir — the
`BoothStub` pattern applied to the emitter.

## Wiring

One call at the end of each run driver:

```lean
materializeIfConfigured "Matroid" "DiscoRun" corpus (pool := pool) (header := …)
```

The destination defaults to `../eureka-corpus` when that directory exists;
`EUREKA_CORPUS_DIR` overrides it, and setting it to the empty string
disables materialization. The header is stamped with the producing
lean-eureka commit (`git rev-parse`, best-effort, dirty trees named as
such).

## Status (as built)

Implemented: `Eureka/Materialize.lean` (renderer, round-trip, quarantine,
aggregator imports), the `origin`/`rung`/`knownAs` metadata on
`Fact`/`FactProposal`, the sibling at `../eureka-corpus`, the CI stub
(`MaterializeStub.lean`), and the `EUREKA_CORPUS_DIR` wiring in `Disco.lean`
and `MatroidDiscoRun.lean`. Two deviations from the sketch below:

- The stub's re-elaboration check runs the emitted file through a **fresh
  `lean` subprocess**, not `runFrontend` in-process — a running Lean cannot
  re-import modules (`enableInitializerExecution`), and the subprocess is
  the sibling's standard anyway. The *materializer's* per-fact round-trip
  check is in-process as designed.
- Run-id collisions are resolved by suffix probing (`Disco`, `Disco_2`, …)
  rather than dates — cumulative-only without a clock dependency.

First materialization: the `Disco.lean` Nat demo, 28/28 facts rendered,
0 quarantined; `lake build` in the sibling succeeds and its audit reports
`audited 28 materialized theorems`. The stub's adversarial case (a
gate-passing fact about un-gated litter) quarantines as specified.

## Implementation steps

1. Sibling skeleton `../eureka-corpus` (lakefile, toolchain, empty root
   import, `Audit.lean`, README). Its own git repo, like LeanDisco.
2. `Eureka/Materialize.lean`: render + round-trip + quarantine + file/import
   writing (~200 lines).
3. `Fact`/`FactProposal` metadata fields; thread `origin`/`rung`/`knownAs`
   in `judge`.
4. `MaterializeStub.lean` (CI): `Nat` corpus → temp dir → re-elaborate the
   emitted text in-process; adversarial case: a fact forced down the
   quarantine path is reported, not written.
5. Wire into `Disco.lean` and one Mathlib driver (`MatroidDiscoRun.lean`);
   run live, `lake build` + audit the sibling, record counts.
