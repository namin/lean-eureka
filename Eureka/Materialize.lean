import Eureka.Concepts

/-!
# Materialization (DESIGN_MATERIALIZE)

A run's corpus dies with the process; materialization writes it as Lean
source into the sibling Lake project (`../eureka-corpus`), the cumulative
library of everything the system has discovered.

The one non-obvious component: the facts were kernel-checked as in-memory
`Expr`s, so rendered source is a *new* artifact. Each statement and proof is
therefore round-tripped at emission time — delaborated, re-parsed,
re-elaborated, and checked against the original — and a fact that does not
survive is quarantined as a comment, never written as a declaration. A fact
whose proof leans on run-local litter (tactic auxiliaries, un-gated helper
declarations) is quarantined too: the sibling imports only its own runs and
the library, so run-local names would not resolve there. The sibling's
`lake build` plus its own axiom audit remain the end-to-end gate.
-/

open Lean Meta Elab

namespace Eureka
namespace Runtime

/-- Where and as what a run materializes. -/
structure MatCfg where
  /-- Root of the sibling project (e.g. `../eureka-corpus`). -/
  dir : System.FilePath
  /-- Domain segment, a valid identifier (e.g. `"Matroid"`, `"Nat"`). -/
  domain : String
  /-- Base run id, a valid identifier; suffixed `_2`, `_3`, … if taken. -/
  runId : String
  /-- Free-text provenance for the file header. -/
  header : String := ""
  /-- Import lines for the run file (the sibling depends on Mathlib). -/
  imports : List String := ["Mathlib"]

structure MatReport where
  file : System.FilePath
  runNs : Name
  conceptsWritten : Nat := 0
  factsWritten : Nat := 0
  /-- Name and reason for everything that did not materialize. -/
  quarantined : Array (Name × String) := #[]

def MatReport.summary (r : MatReport) : String :=
  s!"materialized {r.factsWritten} facts, {r.conceptsWritten} concepts \
to {r.file} (namespace {r.runNs}); {r.quarantined.size} quarantined"

/-- Pretty-print for materialization: full names always; optionally explicit
mode as the retry rung. Proof-term and depth elision are disabled — an
elided `⋯` would just fail the round-trip. -/
private def renderExpr (e : Expr) (explicit : Bool) : MetaM String :=
  withOptions (fun o =>
    let o := o.set `pp.fullNames true
    let o := o.set `pp.deepTerms true
    let o := o.set `pp.proofs true
    let o := o.set `pp.maxSteps 100000
    if explicit then o.set `pp.explicit true else o) do
  return toString (← ppExpr e)

/-- Elaborate rendered source and return the result, absorbing all failures
(cf. `parseConjecture` in the booth — convenience, not trust). -/
private def elabRendered (s : String) (expectedType : Option Expr) :
    MetaM (Option Expr) := do
  match Parser.runParserCategory (← getEnv) `term s with
  | .error _ => return none
  | .ok stx =>
    let savedMsgs := (← getThe Core.State).messages
    let result ← try
        let e ← Term.TermElabM.run' <| Term.withoutErrToSorry do
          let e ← Term.elabTermEnsuringType stx expectedType
          Term.synthesizeSyntheticMVarsNoPostponing
          instantiateMVars e
        if e.hasSorry || e.hasMVar || e.hasFVar then pure none else pure (some e)
      catch _ => pure none
    modifyThe Core.State fun st => { st with messages := savedMsgs }
    return result

/-- The round-trip check for one statement/proof pair: the rendered
statement must elaborate to something definitionally equal to the original,
and the rendered proof must elaborate *at the original statement*. Tried
plain first, then `pp.explicit`. Returns the rendered pair that survived. -/
private def renderChecked (stmt proof : Expr) :
    MetaM (Option (String × String)) := do
  for explicit in [false, true] do
    let r ← attempt do
      let sStr ← renderExpr stmt explicit
      let pStr ← renderExpr proof explicit
      let some s ← elabRendered sStr (some (mkSort .zero)) | return none
      unless ← defeqSafe s stmt do return none
      let some _ ← elabRendered pStr (some stmt) | return none
      return some (sStr, pStr)
    if let some (some rendered) := r then return some rendered
  return none

/-- Same check for a concept: rendered type defeq to the original, rendered
value elaborating at the original type. -/
private def renderCheckedDef (type value : Expr) :
    MetaM (Option (String × String)) := do
  for explicit in [false, true] do
    let r ← attempt do
      let tStr ← renderExpr type explicit
      let vStr ← renderExpr value explicit
      let some t ← elabRendered tStr none | return none
      unless ← defeqSafe t type do return none
      let some _ ← elabRendered vStr (some type) | return none
      return some (tStr, vStr)
    if let some (some rendered) := r then return some rendered
  return none

/-- Constants of `e` that were added by this run rather than imported —
exactly the names that will not resolve in the sibling unless we emit them
ourselves. -/
private def runLocalConsts (e : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  return e.getUsedConstants.filter fun n => (env.getModuleIdxFor? n).isNone

/-- Doc-comment-safe: a stray comment terminator in rendered text must not
close the emitted doc comment early. -/
private def docSafe (s : String) : String :=
  (s.replace "-/" "- /").replace "/-" "/ -"

private def factNote (f : Fact) : String :=
  let rung := if f.rung.isEmpty then "rung unrecorded" else f.rung
  match f.knownAs with
  | some k => s!"origin: {f.origin}; {rung}; grounded: {k}"
  | none => s!"origin: {f.origin}; {rung}"

/-- Append `line` to `path` if no line of the file equals it (creating the
file if needed) — the idempotent aggregator-import update. -/
private def ensureLine (path : System.FilePath) (line : String) : IO Unit := do
  let content ← if ← path.pathExists then IO.FS.readFile path else pure ""
  if (content.splitOn "\n").contains line then return ()
  let content := if content.isEmpty || content.endsWith "\n" then content
                 else content ++ "\n"
  IO.FS.writeFile path (content ++ line ++ "\n")

/-- First `runId`-based file name not already taken — materialization is
cumulative-only; nothing is ever overwritten. -/
private def freshRunId (domainDir : System.FilePath) (base : String) :
    IO String := do
  if !(← (domainDir / s!"{base}.lean").pathExists) then return base
  let mut i := 2
  while ← (domainDir / s!"{base}_{i}.lean").pathExists do
    i := i + 1
  return s!"{base}_{i}"

/-- Materialize a run: emit the concepts the corpus mentions and every fact
that survives the round-trip check into
`<dir>/EurekaCorpus/<domain>/<runId>.lean`, and hook the file into the
aggregator imports. Everything else lands in the quarantine block, counted
and named. -/
def materialize (cfg : MatCfg) (pool : ConceptPool) (corpus : Corpus) :
    MetaM MatReport := do
  -- Pass 1: render every fact (or record why not).
  let mut rendered : Array (Fact × String × String) := #[]
  let mut quarantined : Array (Name × String) := #[]
  for f in corpus.facts do
    match ← renderChecked f.stmt f.proof with
    | some (s, p) => rendered := rendered.push (f, s, p)
    | none =>
      quarantined := quarantined.push (f.name, "statement or proof did not \
round-trip through rendering")
  -- Concepts the rendered facts mention, transitively closed over the pool
  -- (a concept's own body may mention earlier-born concepts). Birth order
  -- is dependency order, so one pass with a growing needed-set suffices.
  let mut neededNames : Array Name := #[]
  for (f, _, _) in rendered do
    for n in (← runLocalConsts f.stmt) ++ (← runLocalConsts f.proof) do
      if pool.concepts.any (·.name == n) && !neededNames.contains n then
        neededNames := neededNames.push n
  let mut closed := true
  while closed do
    closed := false
    for c in pool.concepts do
      if neededNames.contains c.name then
        for n in (← runLocalConsts c.value) ++ (← runLocalConsts c.type) do
          if pool.concepts.any (·.name == n) && !neededNames.contains n then
            neededNames := neededNames.push n
            closed := true
  -- Pass 2: render needed concepts in birth order; a concept that fails
  -- takes its dependents down into quarantine (checked below via emitted).
  let mut concepts : Array (Concept × String × String) := #[]
  let mut emitted : Array Name := #[]
  for c in pool.concepts do
    if neededNames.contains c.name then
      let localOk := (← runLocalConsts c.value).all fun n =>
        emitted.contains n || n == c.name
      if !localOk then
        quarantined := quarantined.push (c.name, "definition mentions \
run-local declarations that did not materialize")
      else
        match ← renderCheckedDef c.type c.value with
        | some (t, v) =>
          concepts := concepts.push (c, t, v)
          emitted := emitted.push c.name
        | none =>
          quarantined := quarantined.push (c.name, "definition did not \
round-trip through rendering")
  -- Pass 3: a fact may only reference run-local names we actually emit —
  -- concepts above, or facts emitted earlier in admission order.
  let mut facts : Array (Fact × String × String) := #[]
  for (f, s, p) in rendered do
    let locals := (← runLocalConsts f.stmt) ++ (← runLocalConsts f.proof)
    match locals.find? (fun n => !emitted.contains n) with
    | some missing =>
      quarantined := quarantined.push (f.name, s!"references run-local \
declaration `{missing}` (tactic auxiliary or un-gated litter) that the \
sibling cannot resolve")
    | none =>
      facts := facts.push (f, s, p)
      emitted := emitted.push f.name
  -- Assemble and write.
  let domainDir := cfg.dir / "EurekaCorpus" / cfg.domain
  IO.FS.createDirAll domainDir
  let runId ← freshRunId domainDir cfg.runId
  let runNs := (((`EurekaCorpus).str cfg.domain).str runId)
  let file := domainDir / s!"{runId}.lean"
  let mut out := ""
  for imp in cfg.imports do
    out := out ++ s!"import {imp}\n"
  out := out ++ s!"\n/-!\nMaterialized by lean-eureka (DESIGN_MATERIALIZE).\n"
  if !cfg.header.isEmpty then
    out := out ++ docSafe cfg.header ++ "\n"
  out := out ++ s!"{facts.size} facts and {concepts.size} concepts \
materialized; {quarantined.size} quarantined below. Every fact was admitted \
through the gate (screen → kernel → axiom audit) in the producing run; this \
file is the *rendered* artifact, and this project's build plus Audit.lean \
re-check it from scratch.\n-/\n\n"
  -- Rendered proof terms routinely bind arguments they discard
  -- (`fun α M e => Iff.symm …`); the lint is noise in generated code.
  out := out ++ "set_option linter.unusedVariables false\n\n"
  out := out ++ s!"namespace {runNs}\n"
  for (c, t, v) in concepts do
    let merged := match c.mergedInto with
      | some m => s!"; merged into {m}"
      | none => ""
    out := out ++ s!"\n/-- invented concept; origin: {c.origin}; \
depth {c.depth}{docSafe merged} -/\n"
    out := out ++ s!"def {c.name} : {t} :=\n  {v}\n"
  for (f, s, p) in facts do
    out := out ++ s!"\n/-- {docSafe (factNote f)} -/\n"
    out := out ++ s!"theorem {f.name} : {s} :=\n  {p}\n"
  out := out ++ s!"\nend {runNs}\n"
  if !quarantined.isEmpty then
    out := out ++ "\n/-!\n## Quarantined — admitted in the run, not materialized\n\n"
    for (n, reason) in quarantined do
      out := out ++ s!"- `{n}`: {docSafe reason}\n"
    out := out ++ "-/\n"
  IO.FS.writeFile file out
  ensureLine (cfg.dir / "EurekaCorpus" / s!"{cfg.domain}.lean")
    s!"import EurekaCorpus.{cfg.domain}.{runId}"
  ensureLine (cfg.dir / "EurekaCorpus.lean")
    s!"import EurekaCorpus.{cfg.domain}"
  return { file, runNs, conceptsWritten := concepts.size,
           factsWritten := facts.size, quarantined }

/-- The producing repo's commit, for the run-file header. Best-effort:
empty when git is unavailable. The clean/dirty verdict is always explicit —
an unqualified stamp would be ambiguous — and "dirty" means modified
*tracked* files: stray untracked files cannot change what a clean checkout
of the commit builds. -/
def gitStamp : IO String := do
  try
    let sha ← IO.Process.output { cmd := "git", args := #["rev-parse", "--short", "HEAD"] }
    if sha.exitCode != 0 then return ""
    let dirty ← IO.Process.output
      { cmd := "git", args := #["status", "--porcelain", "--untracked-files=no"] }
    let verdict := if dirty.exitCode != 0 then "tree state unknown"
      else if dirty.stdout.trim.isEmpty then "clean"
      else "dirty: tracked files modified"
    return s!"lean-eureka commit: {sha.stdout.trim} ({verdict})"
  catch _ => return ""

/-- The driver hook. The destination is `EUREKA_CORPUS_DIR` if set
(set it empty to disable materialization), else `../eureka-corpus` if that
directory exists, else materialization is skipped. The header is stamped
with the producing commit. -/
def materializeIfConfigured (domain runId : String) (corpus : Corpus)
    (pool : ConceptPool := {}) (header : String := "")
    (imports : List String := ["Mathlib"]) : MetaM Unit := do
  let defaultDir : System.FilePath := ".." / "eureka-corpus"
  let dir? ← match (← IO.getEnv "EUREKA_CORPUS_DIR") with
    | some d => pure (if d.isEmpty then none else some (System.FilePath.mk d))
    | none => pure (if ← defaultDir.isDir then some defaultDir else none)
  let some dir := dir? | return ()
  let stamp ← gitStamp
  let header := if stamp.isEmpty then header else s!"{header}\n{stamp}"
  let report ← materialize { dir, domain, runId, header, imports } pool corpus
  IO.println report.summary
  for (n, reason) in report.quarantined do
    IO.println s!"  quarantined {n}: {reason}"

end Runtime
end Eureka
