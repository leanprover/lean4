/-
Copyright (c) 2024 Lean FRO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Ullrich
-/
prelude
import Lean.Elab.Command
import Lean.Linter.Util

namespace Lean.Linter
open Elab.Command

register_builtin_option linter.omit : Bool := {
  defValue := false
  descr := "enable the 'avoid omit' linter"
}

def «omit» : Linter where
  run stx := do
    unless linter.omit.get (← getOptions) do
      return
    if let some stx := stx.find? (·.isOfKind ``Lean.Parser.Command.«omit») then
      logLint linter.omit stx m!"`omit` should be avoided in favor of restructuring your \
        `variable` declarations"

builtin_initialize addLinter «omit»
