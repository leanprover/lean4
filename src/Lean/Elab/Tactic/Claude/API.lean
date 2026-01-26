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

/-- Format an API error response into a user-friendly message -/
def formatAPIError (errorType : String) (message : String) : String :=
  match errorType with
  | "rate_limit_error" =>
    s!"Rate limit exceeded: {message}\n\nTry again in a few moments, or check your usage tier at https://console.anthropic.com"
  | "overloaded_error" =>
    s!"API overloaded: {message}\n\nThe API is temporarily overloaded. Please try again shortly."
  | "authentication_error" =>
    s!"Authentication failed: {message}\n\nCheck that ANTHROPIC_API_KEY is set correctly."
  | "invalid_api_key" =>
    s!"Invalid API key: {message}\n\nVerify your API key at https://console.anthropic.com"
  | "permission_error" =>
    s!"Permission denied: {message}\n\nYour API key may not have access to this model."
  | "not_found_error" =>
    s!"Model not found: {message}\n\nCheck the model name in tactic.claude.model option."
  | "invalid_request_error" =>
    s!"Invalid request: {message}"
  | _ =>
    s!"API error ({errorType}): {message}"

/-- Check if JSON response is an error and extract error details -/
def checkAPIError (json : Json) : Option (String × String) := do
  let errorObj ← json.getObjVal? "error" |>.toOption
  let errorType ← errorObj.getObjValAs? String "type" |>.toOption
  let message ← errorObj.getObjValAs? String "message" |>.toOption
  return (errorType, message)

/-- Call Anthropic Messages API and return (content, inputTokens, outputTokens).
    The timeout parameter specifies the maximum time in seconds (0 = no timeout). -/
def callClaudeAPI (prompt : String) (model : String) (timeout : Nat := 60) : IO (String × Nat × Nat) := do
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

  -- Build curl args with optional timeout
  let timeoutArgs : Array String := if timeout > 0 then
    #["--connect-timeout", toString timeout, "--max-time", toString timeout]
  else
    #[]

  -- Call curl
  let output ← IO.Process.output {
    cmd := "curl"
    args := timeoutArgs ++ #[
      "-s", "-X", "POST",
      "https://api.anthropic.com/v1/messages",
      "-H", s!"x-api-key: {apiKey}",
      "-H", "anthropic-version: 2023-06-01",
      "-H", "content-type: application/json",
      "-d", toString requestBody
    ]
  }

  if output.exitCode != 0 then
    -- Exit code 28 is curl's timeout error
    if output.exitCode == 28 then
      throw <| .userError s!"API request timed out after {timeout} seconds"
    throw <| .userError s!"curl failed: {output.stderr}"

  -- Parse response
  let json ← match Json.parse output.stdout with
    | .ok j => pure j
    | .error err => throw <| IO.userError s!"Failed to parse API response: {err}"

  -- Check for API error response
  if let some (errorType, message) := checkAPIError json then
    throw <| IO.userError (formatAPIError errorType message)

  -- Extract content from successful response
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
