/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
prelude
import Lean.Elab.Command

/-!
# Defines `#time` command.

Time the elaboration of a command, and print the result (in milliseconds).
-/

namespace Lean.Elab.Time

open Command

@[builtin_command_elab Lean.Parser.timeCmd] def elabTimeCmd : CommandElab
  | `(#time%$tk $stx:command) => do
    let start ← IO.monoMsNow
    elabCommand stx
    logInfoAt tk m!"time: {(← IO.monoMsNow) - start}ms"
  | _ => throwUnsupportedSyntax

end Lean.Elab.Time
