/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.System.IO
public import Lean.Data.Json

public section

namespace Lean.Elab.Tactic.Claude.API

open Lean

/-! ## Anthropic API Backend -/

/-- Call Anthropic Messages API and return (content, inputTokens, outputTokens) -/
def callClaudeAPI (prompt : String) (model : String) : IO (String × Nat × Nat) := do
  let some apiKey ← IO.getEnv "ANTHROPIC_API_KEY"
    | throw <| .userError "ANTHROPIC_API_KEY not set"

  -- Build JSON request
  let requestBody := Json.mkObj [
    ("model", Json.str model),
    ("max_tokens", Json.num 1024),
    ("messages", Json.arr #[
      Json.mkObj [
        ("role", Json.str "user"),
        ("content", Json.str prompt)
      ]
    ])
  ]

  -- Call curl
  let output ← IO.Process.output {
    cmd := "curl"
    args := #[
      "-s", "-X", "POST",
      "https://api.anthropic.com/v1/messages",
      "-H", s!"x-api-key: {apiKey}",
      "-H", "anthropic-version: 2023-06-01",
      "-H", "content-type: application/json",
      "-d", toString requestBody
    ]
  }

  if output.exitCode != 0 then
    throw <| .userError s!"curl failed: {output.stderr}"

  -- Parse response
  let json ← match Json.parse output.stdout with
    | .ok j => pure j
    | .error err => throw <| IO.userError s!"Failed to parse API response: {err}"

  -- Extract content from response
  let content ← match json.getObjVal? "content" with
    | .ok c => pure c
    | .error err => throw <| IO.userError s!"No 'content' field in response: {err}\n\nFull response:\n{json}"

  let contentArr ← match content.getArr? with
    | .ok arr => pure arr
    | .error err => throw <| IO.userError s!"Content is not an array: {err}"

  let firstContent ← match contentArr[0]? with
    | some c => pure c
    | none => throw <| IO.userError "Content array is empty"

  let text ← match firstContent.getObjVal? "text" with
    | .ok t => pure t
    | .error err => throw <| IO.userError s!"No 'text' field in content: {err}"

  let textStr ← match text.getStr? with
    | .ok s => pure s
    | .error err => throw <| IO.userError s!"Text is not a string: {err}"

  -- Extract token counts
  let usage ← match json.getObjVal? "usage" with
    | .ok u => pure u
    | .error _ => pure <| Json.mkObj []  -- If no usage, use empty object

  let inputTokens ← match usage.getObjVal? "input_tokens" with
    | .ok t => match t.getNat? with
      | .ok n => pure n
      | .error _ => pure 0
    | .error _ => pure 0

  let outputTokens ← match usage.getObjVal? "output_tokens" with
    | .ok t => match t.getNat? with
      | .ok n => pure n
      | .error _ => pure 0
    | .error _ => pure 0

  return (textStr, inputTokens, outputTokens)

end Lean.Elab.Tactic.Claude.API
