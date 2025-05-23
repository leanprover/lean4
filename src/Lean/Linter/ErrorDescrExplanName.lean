/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Command
import Lean.Linter.Util
import Lean.Server.InfoUtils

namespace Lean.Linter

open Elab

register_builtin_option linter.errorDescrExplanationName : Bool := {
  defValue := false
  descr := "if true, generate warnings when declaring an error descriptor with \
    an associated explanation name that does not exist."
}

def errorDescrExplanationName : Linter where
  run stx := do
    unless linter.errorDescrExplanationName.get (← getOptions) do
      return
    let trees ← getInfoTrees
    for tree in trees do
      logInfo m!"{← tree.format}"
      let c ← tree.visitM' (preNode := fun ci info children => do
        let .ofCommandInfo cmdInfo := info | pure true
        return false
        )
      -- logInfo m!"{c}"
      -- let some range := info.range? | return

builtin_initialize addLinter errorDescrExplanationName
