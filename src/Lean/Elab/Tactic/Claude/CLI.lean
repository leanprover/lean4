/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.System.IO

public section

namespace Lean.Elab.Tactic.Claude.CLI

open Lean

/-! ## Claude CLI Backend -/

/-- Check if a command exists in PATH -/
private def commandExists (cmd : String) : IO Bool := do
  let output ← IO.Process.output {
    cmd := "which"
    args := #[cmd]
  }
  return output.exitCode == 0

/-- Call Claude CLI and return response.
    The timeout parameter specifies the maximum time in seconds (0 = no timeout). -/
def callClaudeCLI (prompt : String) (timeout : Nat := 60) : IO String := do
  -- Try to use timeout command if available and timeout > 0
  let (cmd, args) ← if timeout > 0 then do
    -- Try `timeout` (Linux, some macOS), then `gtimeout` (macOS via homebrew)
    if ← commandExists "timeout" then
      pure ("timeout", #[toString timeout, "claude", "-p", prompt])
    else if ← commandExists "gtimeout" then
      pure ("gtimeout", #[toString timeout, "claude", "-p", prompt])
    else
      pure ("claude", #["-p", prompt])
  else
    pure ("claude", #["-p", prompt])

  let output ← IO.Process.output {
    cmd := cmd
    args := args
    stdin := .null
    stdout := .piped
    stderr := .piped
  }

  if output.exitCode != 0 then
    -- Exit code 124 is timeout's signal that the command timed out
    if output.exitCode == 124 then
      throw <| .userError s!"claude CLI timed out after {timeout} seconds"
    let errorMsg := if output.stderr.isEmpty then output.stdout else output.stderr
    throw <| .userError s!"claude CLI failed (exit code {output.exitCode}): {errorMsg}"

  return output.stdout

end Lean.Elab.Tactic.Claude.CLI
