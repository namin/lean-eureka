import Lean.Data.Json

/-!
# Bedrock client

Ported from lean-sage's `LeanBlack/Bedrock.lean` (itself from lean-green,
the artifact that first ran an LLM proposer from inside Lean). Wraps
`aws bedrock-runtime invoke-model`; request body and response go through
temp files. Requires the `aws` CLI on PATH, credentials in the standard
chain, and Bedrock access in the configured region.

The LLM is a proposer: everything it returns is untrusted text that must
survive parsing, elaboration, counterexample search, and the gate.
-/

namespace Eureka
namespace LLM

open Lean (Json toJson)

structure Config where
  region    : String := "us-east-1"
  modelId   : String := "us.anthropic.claude-sonnet-5"
  maxTokens : Nat    := 16000
  thinking  : Bool   := false
  effort    : Option String := none
  bodyPath  : String := "/tmp/lean-eureka-bedrock-body.json"
  outPath   : String := "/tmp/lean-eureka-bedrock-out.json"

/-- Proposal-shaped calls (the concept booth): no thinking, the reply is
a cheap formatted line. -/
def defaultConfig : Config := {}

/-- Reasoning-shaped calls (the prover's repair rung): adaptive thinking
capped at medium effort — on unprovable goals deliberation otherwise
expands to fill any `max_tokens` (measured: 31993 of 32000 tokens spent
thinking, no answer ever started) — with output headroom so a real think
never starves the answer. -/
def proverConfig : Config :=
  { thinking := true, maxTokens := 32000, effort := some "medium" }

private def bodyJson (cfg : Config) (prompt : String) : Json :=
  let fields := [
    ("anthropic_version", Json.str "bedrock-2023-05-31"),
    ("thinking", Json.mkObj
      [("type", Json.str (if cfg.thinking then "adaptive" else "disabled"))]),
    ("max_tokens", toJson cfg.maxTokens),
    ("messages", Json.arr #[
      Json.mkObj [("role", Json.str "user"), ("content", Json.str prompt)]
    ])
  ]
  let fields := match cfg.effort with
    | some e => fields ++ [("output_config", Json.mkObj [("effort", Json.str e)])]
    | none => fields
  Json.mkObj fields

/-- Concatenate every `text` block in the response (the content array may
lead with a `thinking` block, which has no `text` field). -/
private def extractText (j : Json) : Except String String := do
  let content ← j.getObjVal? "content"
  let arr ← content.getArr?
  let texts := arr.filterMap fun b =>
    match b.getObjVal? "text" >>= Json.getStr? with
    | .ok s => some s
    | .error _ => none
  let joined := texts.foldl (· ++ ·) ""
  if joined.isEmpty then
    .error "no text block in response.content"
  else
    .ok joined

/-- Wrap any transport with a JSONL transcript sink (DESIGN_RECORD R1):
one line per call — `{tag, i, prompt, response | error}` — appended in
call order. Index-ordered, no timestamps (determinism rules). The
record the live runs were losing. -/
def withTranscript (path : System.FilePath) (tag : String)
    (call : String → IO (Except String String)) :
    IO (String → IO (Except String String)) := do
  let counter ← IO.mkRef 0
  return fun prompt => do
    let r ← call prompt
    let i ← counter.get
    counter.set (i + 1)
    let payload := match r with
      | .ok t => ("response", Json.str t)
      | .error e => ("error", Json.str e)
    let entry := Json.mkObj
      [("tag", Json.str tag), ("i", toJson i),
       ("prompt", Json.str prompt), payload]
    if let some d := path.parent then
      IO.FS.createDirAll d
    IO.FS.withFile path .append fun h => h.putStrLn entry.compress
    return r

/-- One Bedrock call: the model's text, or an error describing what went
wrong (CLI failure, JSON parse, unexpected response shape). -/
def invoke (cfg : Config) (prompt : String) : IO (Except String String) := do
  IO.FS.writeFile cfg.bodyPath (bodyJson cfg prompt).pretty
  let out ← IO.Process.output {
    cmd := "aws"
    args := #[
      "bedrock-runtime", "invoke-model",
      "--cli-read-timeout", "600",
      "--region", cfg.region,
      "--model-id", cfg.modelId,
      "--content-type", "application/json",
      "--body", "fileb://" ++ cfg.bodyPath,
      cfg.outPath
    ]
  }
  if out.exitCode != 0 then
    return .error s!"aws CLI failed (exit {out.exitCode}):\n{out.stderr}"
  let respText ← IO.FS.readFile cfg.outPath
  match Json.parse respText with
  | .error e => return .error s!"JSON parse failed: {e}\nresponse was: {respText}"
  | .ok json => return extractText json

end LLM
end Eureka
