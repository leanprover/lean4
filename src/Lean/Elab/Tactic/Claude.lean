/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Lean.Elab.Tactic.Claude.Basic
public import Lean.Elab.Tactic.Claude.Template
public import Lean.Elab.Tactic.Claude.API
public import Lean.Elab.Tactic.Claude.CLI
meta import Lean.Parser.Tactic

public section

namespace Lean.Elab.Tactic

open Lean Meta Elab.Tactic Claude

/-! ## Claude Tactic -/

/--
Calls Claude AI to suggest tactics for the current goal.

Claude analyzes the goal, current declaration, and file context, then suggests
tactics that are tested for validity before being presented as "Try this:" suggestions.

## Activation

The tactic requires one of the following environment variable configurations:

- **API backend**: Set `ANTHROPIC_API_KEY` and `LEAN_CLAUDE_API=true`
- **CLI backend**: Set `LEAN_CLAUDE_CODE=true` (requires Claude Code CLI)

## Options

- `set_option tactic.claude.model "claude-sonnet-4-20250514"` - Choose model (default: Opus)
- `set_option tactic.claude.template "/path/to/template.txt"` - Custom prompt template
- `set_option tactic.claude.timeout 60` - Timeout in seconds (default: 60, 0 = no timeout)
- `set_option trace.claude.prompt true` - Show the prompt sent to Claude

## Usage Notes

This tactic is primarily intended for automation (e.g., as a fallback in `try?`).
For interactive proof development, running a Claude Code session alongside your editor
provides a more effective workflow with full conversation context.
-/
syntax (name := claude) "claude" (str)? : tactic

/-- Main tactic implementation. -/
@[builtin_tactic Lean.Elab.Tactic.claude]
def evalClaude : Tactic := fun stx => do
  -- 0. Extract optional instruction string
  let instruction? : Option String :=
    if stx[1].isNone then none
    else stx[1][0].isStrLit?

  -- 0b. Validate punctuation if non-empty string is provided
  if let some instr := instruction? then
    let trimmed := instr.trimAsciiEnd.toString
    if !trimmed.isEmpty then
      if !['.', '!', '?'].contains trimmed.back then
        logWarning "Instruction should end with punctuation (., !, or ?). Skipping Claude query."
        return

  -- 1. Load config
  let config ← Claude.getConfig

  -- 2. Select backend (mock/API/CLI)
  let backend ← Claude.selectBackend config

  -- 3. Get current goal
  let goal ← getMainGoal

  -- 4. Load and interpolate template
  let templateContent ← Claude.loadTemplateContent config.templatePath
  let template := Claude.parseTemplate templateContent
  let ctx ← Claude.buildTemplateContext goal
  let prompt ← Claude.interpolateTemplate template ctx

  -- 4b. Append instruction if provided
  let prompt := match instruction? with
    | some instr => if instr.trimAsciiEnd.toString.isEmpty then prompt else prompt ++ "\n\n" ++ instr
    | none => prompt

  -- 5. Trace if enabled
  if config.tracePrompt then
    logInfo m!"Claude prompt:\n{prompt}"

  -- 6. Call backend
  let (response, tokenInfo?) ← match backend with
    | .mock resp =>
      pure (resp, none)
    | .api =>
      let (content, inTokens, outTokens) ← Claude.API.callClaudeAPI prompt config.model config.timeout
      pure (content, some (inTokens, outTokens))
    | .cli =>
      let content ← Claude.CLI.callClaudeCLI prompt config.timeout
      pure (content, none)

  -- 7. Parse JSON response
  let tacticResp ← match Claude.parseTacticResponse response with
    | .ok resp => pure resp
    | .error err =>
      throwError s!"Failed to parse Claude response: {err}\n\nResponse:\n{response}"

  -- 8. Evaluate tactics
  let successful ← Claude.evaluateTactics tacticResp.tactics

  -- 9. Generate "Try this:" suggestions
  Claude.generateSuggestions successful

  -- 10. Show usage info
  if let some (inTokens, outTokens) := tokenInfo? then
    logInfo m!"API usage: {inTokens} input tokens, {outTokens} output tokens"
  else if backend == .cli then
    logInfo "Run /usage in Claude Code to check usage"

end Lean.Elab.Tactic
