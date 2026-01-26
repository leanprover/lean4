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
public import Init.Data.String.Search

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

/-- Timeout in seconds for API/CLI calls (0 = no timeout) -/
register_builtin_option tactic.claude.timeout : Nat := {
  defValue := 60
  descr := "Timeout in seconds for API/CLI calls (0 = no timeout)"
}

/-! ## Configuration -/

structure Config where
  templatePath : String
  model : String
  mock : String
  tracePrompt : Bool
  timeout : Nat
  deriving Inhabited

def getConfig : TacticM Config := do
  let opts ← getOptions
  return {
    templatePath := tactic.claude.template.get opts
    model := tactic.claude.model.get opts
    mock := tactic.claude.mock.get opts
    tracePrompt := trace.claude.prompt.get opts
    timeout := tactic.claude.timeout.get opts
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

/-- Extract JSON object by finding matching braces, respecting string literals.
    Given a string starting with `{`, returns the JSON object up to and including the matching `}`. -/
private def extractJsonObject (s : String) : Option String := Id.run do
  let mut depth : Int := 0
  let mut inString := false
  let mut prevBackslash := false
  let mut pos := 0
  for c in s.toList do
    pos := pos + 1
    if inString then
      if c == '\\' && !prevBackslash then
        prevBackslash := true
      else
        if c == '"' && !prevBackslash then
          inString := false
        prevBackslash := false
    else
      if c == '"' then
        inString := true
      else if c == '{' then
        depth := depth + 1
      else if c == '}' then
        depth := depth - 1
        if depth == 0 then
          return some (s.take pos).toString
  return none

/-- Find the substring starting at the first occurrence of `pattern` in `s`.
    Returns everything from the pattern onwards, or `none` if not found. -/
private def findSubstringFrom (s : String) (pattern : String) : Option String :=
  (s.find? pattern).map fun pos => pos.offset.extract s s.rawEndPos

/-- Extract JSON from a response that may contain explanation text.
    Tries several strategies:
    1. Look for ```json code block
    2. Look for any code block containing "tactics"
    3. Find {"tactics": pattern directly in text
    4. Fall back to trimmed original response -/
def extractJson (response : String) : String := Id.run do
  -- Collect all code blocks with their language tags
  let lines := (response.split (· == '\n')).toArray
  let mut inBlock := false
  let mut currentLang := ""
  let mut currentLines : Array String := #[]
  let mut blocks : Array (String × String) := #[]

  for line in lines do
    let trimmed := line.trimAscii
    if trimmed.startsWith "```" && !inBlock then
      inBlock := true
      currentLang := trimmed.drop 3 |>.trimAscii.toString
      currentLines := #[]
    else if trimmed.startsWith "```" && inBlock then
      let content := "\n".intercalate currentLines.toList
      blocks := blocks.push (currentLang, content)
      inBlock := false
      currentLang := ""
      currentLines := #[]
    else if inBlock then
      currentLines := currentLines.push line.toString

  -- Strategy 1: Look for ```json code block
  for (lang, content) in blocks do
    if lang == "json" then
      return content.trimAscii.toString

  -- Strategy 2: Look for any code block containing "tactics"
  for (_, content) in blocks do
    if content.contains "\"tactics\"" then
      return content.trimAscii.toString

  -- Strategy 3: Find {"tactics" pattern directly in text (without code block)
  if let some jsonStart := findSubstringFrom response "{\"tactics\"" then
    if let some json := extractJsonObject jsonStart then
      return json

  -- Also try with space: { "tactics"
  if let some jsonStart := findSubstringFrom response "{ \"tactics\"" then
    if let some json := extractJsonObject jsonStart then
      return json

  -- Fallback: return trimmed original (for pure JSON responses)
  return response.trimAscii.toString

/-- Parse JSON response: `{"tactics": ["tactic1", "tactic2", ...]}` -/
def parseTacticResponse (response : String) : Except String TacticResponse := do
  -- Extract JSON from response (handles markdown code blocks, explanation text, etc.)
  let cleanResponse := extractJson response
  let json ← Lean.Json.parse cleanResponse
  let tacticsJson ← json.getObjVal? "tactics"
  let tacticsArr ← tacticsJson.getArr?
  let tactics ← tacticsArr.mapM (·.getStr?)
  return { tactics := tactics }

/-! ## Tactic Evaluation -/

/-- Check that no assigned goals contain sorry in their assignments.
    Type errors during elaboration create synthetic sorries, so this also
    catches type mismatches. -/
def assignmentsHaveNoSorry (goals : List MVarId) : MetaM Bool := do
  for goal in goals do
    if let some assignment ← getExprMVarAssignment? goal then
      if assignment.hasSorry then
        return false
  return true

/-- Try a tactic and return whether it succeeded (without committing changes).
    Verifies that:
    1. Goal assignments don't contain sorry (catches type errors that assign synthetic sorry)
    2. No error messages were logged during evaluation (catches errors logged via recover mode)
    Uses `withCapturedMessages` to inspect the message log without polluting it. -/
def tryTactic (stx : Syntax) : TacticM Bool := do
  let savedState ← saveState
  let goalsBefore ← getGoals
  try
    let ((), newMsgs) ← withCapturedMessages do
      evalTactic stx
    let valid ← assignmentsHaveNoSorry goalsBefore
    savedState.restore
    return valid && !hasErrorMessages newMsgs
  catch _ =>
    savedState.restore
    return false

/-- Run a parser on a string. Based on `runParserCategory` but takes a Parser directly.
    See https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/quickest.20path.20from.20.60String.60.20to.20.60.60TSyntax.20.60tacticSeq.60.60
    where Sebastian Ullrich confirms there's no direct API for this. -/
def runParser (env : Environment) (parser : Parser.Parser) (input : String) (fileName := "<input>") : Except String Syntax :=
  let p := Parser.andthenFn Parser.whitespace parser.fn
  let ictx := Parser.mkInputContext input fileName
  let s := p.run ictx { env, options := {} } (Parser.getTokenTable env) (Parser.mkParserState input)
  if !s.allErrors.isEmpty then
    .error (s.toErrorMsg ictx)
  else if ictx.atEnd s.pos then
    .ok s.stxStack.back
  else
    .error ((s.mkError "end of input").toErrorMsg ictx)

/-- Evaluate tactics from strings, returning those that succeed.
    Returns pairs of (original string, parsed syntax) to preserve formatting. -/
def evaluateTactics (tactics : Array String) : TacticM (Array (String × Syntax)) := do
  let env ← getEnv
  let mut successful := #[]

  for tacStr in tactics do
    -- For multi-line tactics, use tacticSeq parser; for single-line, use tactic category
    let parseResult := if tacStr.contains '\n' then
      runParser env Parser.Tactic.tacticSeq tacStr
    else
      Parser.runParserCategory env `tactic tacStr

    match parseResult with
    | .ok stx =>
      if ← tryTactic stx then
        successful := successful.push (tacStr, stx)
    | .error _ =>
      -- Skip tactics that don't parse
      continue

  return successful

/-! ## Suggestion Generation -/

/-- Generate "Try this:" suggestions -/
def generateSuggestions (successful : Array (String × Syntax)) : TacticM Unit := do
  if successful.isEmpty then
    throwError "Claude suggested no working tactics"

  -- Show suggestions using original string to preserve formatting (especially newlines)
  let suggestionObjs : Array Tactic.TryThis.Suggestion :=
    successful.map fun (tacStr, _stx) => { suggestion := .string tacStr }
  if suggestionObjs.size == 1 then
    Tactic.TryThis.addSuggestion (← getRef) suggestionObjs[0]!
  else
    Tactic.TryThis.addSuggestions (← getRef) suggestionObjs

end Lean.Elab.Tactic.Claude
