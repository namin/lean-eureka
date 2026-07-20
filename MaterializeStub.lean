import Eureka

/-!
Materialization test, deterministic, no credentials (DESIGN_MATERIALIZE).
A small `Nat` corpus is materialized to a scratch directory and the emitted
file is re-elaborated from scratch (`runFrontend`) — the same standard the
sibling's `lake build` applies, run here against the rendered text. The
adversarial case: a fact whose proof leans on run-local litter (a helper
declaration that entered the environment outside the gates) passes the fact
gate but cannot resolve in the sibling — it must be quarantined, not
written. Run with `lake env lean MaterializeStub.lean`.
-/

open Lean Meta Eureka.Runtime

def stubDir : System.FilePath := ".materialize-stub"

#eval show MetaM Unit from do
  if ← stubDir.pathExists then IO.FS.removeDirAll stubDir
  -- A small deterministic corpus.
  let corpus ← discover [identityH, commH] (generations := 1)
  -- The adversarial fact: `litterHelper` is honest litter — added by raw
  -- `addDecl`, not gate-admitted — so a fact about it passes the gate (the
  -- proof is `rfl`, the audit is clean) yet cannot materialize.
  addDecl <| .defnDecl
    { name := `litterHelper, levelParams := [], type := mkConst ``Nat,
      value := mkNatLit 0, hints := .abbrev, safety := .safe }
  let stmt ← mkEq (mkConst `litterHelper) (mkNatLit 0)
  let proof ← mkEqRefl (mkConst `litterHelper)
  let nm ← freshName `litter_fact
  let some litter ← commitFact
      { name := nm, stmt, proof, origin := `stub, rung := "refl" }
    | throwError "stub: the litter fact should pass the gate"
  let corpus := { corpus with facts := corpus.facts.push litter }
  -- Materialize.
  let report ← materialize
    { dir := stubDir, domain := "Nat", runId := "Stub", imports := [],
      header := "Producing run: MaterializeStub.lean (deterministic CI stub)." }
    {} corpus
  IO.println ""
  IO.println report.summary
  for (n, reason) in report.quarantined do
    IO.println s!"  quarantined {n}: {reason}"
  -- The litter fact is quarantined, everything else is written.
  unless report.quarantined.any (·.1 == litter.name) do
    throwError "stub: the litter fact should have been quarantined"
  unless report.factsWritten == corpus.facts.size - 1 do
    throwError "stub: expected every fact but the litter one to materialize \
({report.factsWritten} of {corpus.facts.size})"
  -- The emitted file re-elaborates from scratch, by the actual compiler in
  -- a fresh process — the sibling's standard.
  let content ← IO.FS.readFile report.file
  unless (content.splitOn "theorem ").length - 1 == report.factsWritten do
    throwError "stub: emitted theorem count does not match the report"
  let out ← IO.Process.output { cmd := "lean", args := #[report.file.toString] }
  unless out.exitCode == 0 do
    throwError "stub: the emitted file failed to re-elaborate:\n{out.stderr}\n{out.stdout}"
  IO.println "emitted file re-elaborated cleanly from scratch (fresh `lean` process)"
  -- Aggregator imports landed, idempotently.
  let root ← IO.FS.readFile (stubDir / "EurekaCorpus.lean")
  let dom ← IO.FS.readFile (stubDir / "EurekaCorpus" / "Nat.lean")
  unless (root.splitOn "\n").contains "import EurekaCorpus.Nat" do
    throwError "stub: root aggregator import missing"
  unless (dom.splitOn "\n").contains "import EurekaCorpus.Nat.Stub" do
    throwError "stub: domain aggregator import missing"
  -- A second materialization never overwrites: it lands in Stub_2.
  let report2 ← materialize
    { dir := stubDir, domain := "Nat", runId := "Stub", imports := [] } {} corpus
  unless report2.runNs != report.runNs do
    throwError "stub: re-materialization should get a fresh run id"
  IO.println s!"re-materialization landed in {report2.runNs} — cumulative, \
nothing overwritten"
  IO.println "stub OK"
