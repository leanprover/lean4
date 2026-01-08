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

/-- Call Claude CLI and return response -/
def callClaudeCLI (prompt : String) : IO String := do
  -- Call: claude -p "prompt"
  let output ← IO.Process.output {
    cmd := "claude"
    args := #["-p", prompt]
    stdin := .null
    stdout := .piped
    stderr := .piped
  }

  if output.exitCode != 0 then
    let errorMsg := if output.stderr.isEmpty then output.stdout else output.stderr
    throw <| .userError s!"claude CLI failed (exit code {output.exitCode}): {errorMsg}"

  return output.stdout

end Lean.Elab.Tactic.Claude.CLI
