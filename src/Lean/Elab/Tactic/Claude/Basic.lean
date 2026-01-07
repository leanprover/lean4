/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Elab.Tactic.Basic
public import Lean.Meta.Tactic.TryThis
public import Init.System.IO

public section

namespace Lean.Elab.Tactic.Claude

open Lean Meta Elab.Tactic

/-!
# Claude Tactic

The `claude` tactic calls Claude AI (via API or CLI) to suggest tactics for the current goal.

## Template Variables

Templates support the following variables (computed lazily):
- `{goal}` - Pretty-printed current goal
- `{declaration}` - Current declaration source text
- `{file_prefix}` - File content before current position
- `{suggestions}` - Library suggestion names and scores
- `{suggestions_types}` - Library suggestions with their types
- `{lean_version}` - Lean version string

## Environment Variables

Backend selection is controlled by environment variables:
- API backend: Set `ANTHROPIC_API_KEY` and `LEAN_CLAUDE_API=true`
- CLI backend: Set `LEAN_CLAUDE_CODE=true`

-/

/-- Path to custom template file (empty = use default template) -/
register_builtin_option tactic.claude.template : String := {
  defValue := ""
  descr := "Path to custom template file (empty = use default)"
}

/-- Claude model to use for API requests -/
register_builtin_option tactic.claude.model : String := {
  defValue := "claude-opus-4-20250514"
  descr := "Claude model to use (e.g., claude-opus-4-20250514, claude-sonnet-4-20250514)"
}

/-- Mock JSON response for testing -/
register_builtin_option tactic.claude.mock : String := {
  defValue := ""
  descr := "Mock JSON response for testing"
}

/-- Trace the prompt sent to Claude -/
register_builtin_option trace.claude.prompt : Bool := {
  defValue := false
  descr := "Trace the prompt sent to Claude"
}

/-! ## Configuration -/

structure Config where
  templatePath : String
  model : String
  mock : String
  tracePrompt : Bool
  deriving Inhabited

def getConfig : TacticM Config := do
  let opts ← getOptions
  return {
    templatePath := tactic.claude.template.get opts
    model := tactic.claude.model.get opts
    mock := tactic.claude.mock.get opts
    tracePrompt := trace.claude.prompt.get opts
  }

/-! ## Backend Selection -/

inductive Backend where
  | api
  | cli
  | mock (response : String)
  deriving Repr, BEq

def selectBackend (config : Config) : IO Backend := do
  -- Priority: mock > API > CLI
  if config.mock != "" then
    return .mock config.mock

  -- Check for API backend
  let apiKey? ← IO.getEnv "ANTHROPIC_API_KEY"
  let apiEnabled? ← IO.getEnv "LEAN_CLAUDE_API"

  if apiKey?.isSome && apiEnabled? == some "true" then
    return .api

  -- Check for CLI backend
  let cliEnabled? ← IO.getEnv "LEAN_CLAUDE_CODE"
  if cliEnabled? == some "true" then
    return .cli

  -- No backend available
  throw <| .userError "Claude tactic requires either (ANTHROPIC_API_KEY + LEAN_CLAUDE_API=true) or LEAN_CLAUDE_CODE=true"

/-! ## Response Parsing -/

structure TacticResponse where
  tactics : Array String
  deriving Inhabited

/-- Strip markdown code block wrapper if present (simple fallback in case Claude adds them) -/
def stripMarkdownCodeBlock (response : String) : String := Id.run do
  -- Very simple approach: if response contains ```, try to extract JSON from between fences
  if !response.contains "```" then
    return response

  -- Split response into lines
  let lines := (response.split (· == '\n')).toArray
  -- Find line with opening ```
  let mut inBlock := false
  let mut jsonLines := #[]

  for line in lines do
    let lineStr := line.toString.trimAscii.toString
    if lineStr.startsWith "```" && !inBlock then
      -- Start of code block
      inBlock := true
    else if lineStr.startsWith "```" && inBlock then
      -- End of code block
      break
    else if inBlock then
      -- Inside code block
      jsonLines := jsonLines.push line.toString

  if jsonLines.isEmpty then
    return response
  else
    return "\n".intercalate jsonLines.toList

/-- Parse JSON response: `{"tactics": ["tactic1", "tactic2", ...]}` -/
def parseTacticResponse (response : String) : Except String TacticResponse := do
  -- Strip markdown code block if present
  let cleanResponse := stripMarkdownCodeBlock response
  let json ← Lean.Json.parse cleanResponse
  let tacticsJson ← json.getObjVal? "tactics"
  let tacticsArr ← tacticsJson.getArr?
  let tactics ← tacticsArr.mapM (·.getStr?)
  return { tactics := tactics }

/-! ## Tactic Evaluation -/

/-- Try a tactic and return whether it succeeded (without committing changes) -/
def tryTactic (stx : Syntax) : TacticM Bool := do
  let savedState ← saveState
  try
    evalTactic stx
    savedState.restore
    return true
  catch _ =>
    savedState.restore
    return false

/-- Evaluate tactics from strings, returning those that succeed -/
def evaluateTactics (tactics : Array String) : TacticM (Array (TSyntax `tactic)) := do
  let env ← getEnv
  let mut successful := #[]

  for tacStr in tactics do
    -- Parse tactic string (may contain newlines for multi-step sequences)
    match Parser.runParserCategory env `tactic tacStr with
    | .ok stx =>
      -- Try the tactic
      if ← tryTactic stx then
        successful := successful.push ⟨stx⟩
    | .error _ =>
      -- Skip invalid tactics
      continue

  return successful

/-! ## Suggestion Generation -/

/-- Generate "Try this:" suggestions -/
def generateSuggestions (successful : Array (TSyntax `tactic)) : TacticM Unit := do
  if successful.isEmpty then
    throwError "Claude suggested no working tactics"

  -- Show suggestions
  let suggestionObjs : Array Tactic.TryThis.Suggestion :=
    successful.map fun (s : TSyntax `tactic) => { suggestion := .tsyntax s }
  if suggestionObjs.size == 1 then
    Tactic.TryThis.addSuggestion (← getRef) suggestionObjs[0]!
  else
    Tactic.TryThis.addSuggestions (← getRef) suggestionObjs

end Lean.Elab.Tactic.Claude
