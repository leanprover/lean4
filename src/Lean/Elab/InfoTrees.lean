/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Lean.Elab.Command

open Lean Elab Command

namespace Lean.Elab.Tactic.InfoTrees

@[builtin_command_elab infoTreesCmd, inherit_doc guardMsgsCmd]
def elabInfoTrees : CommandElab
  | `(command| #info_trees%$tk in $cmd) => do
    if ! (← getInfoState).enabled then
      logError "Info trees are disabled, can not use `#info_trees`."
    else
      elabCommand cmd
      let infoTrees ← getInfoTrees
      for t in infoTrees do
        logInfoAt tk (← t.format)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic.InfoTrees
