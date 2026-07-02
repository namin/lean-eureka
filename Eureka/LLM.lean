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
  bodyPath  : String := "/tmp/lean-eureka-bedrock-body.json"
  outPath   : String := "/tmp/lean-eureka-bedrock-out.json"

def defaultConfig : Config := {}

private def bodyJson (cfg : Config) (prompt : String) : Json :=
  Json.mkObj [
    ("anthropic_version", Json.str "bedrock-2023-05-31"),
    ("max_tokens", toJson cfg.maxTokens),
    ("messages", Json.arr #[
      Json.mkObj [("role", Json.str "user"), ("content", Json.str prompt)]
    ])
  ]

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
