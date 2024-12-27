/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Tactics
import Lean.Meta.Tactic.Grind
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Tactic
open Meta

def grind (mvarId : MVarId) (mainDeclName : Name) : MetaM Unit := do
  let mvarIds ← Grind.main mvarId mainDeclName
  unless mvarIds.isEmpty do
    throwError "`grind` failed\n{goalsToMessageData mvarIds}"

@[builtin_tactic Lean.Parser.Tactic.grind] def evalApplyRfl : Tactic := fun stx => do
  match stx with
  | `(tactic| grind) =>
    logWarningAt stx "The `grind` tactic is experimental and still under development. Avoid using it in production projects"
    let declName := (← Term.getDeclName?).getD `_grind
    withMainContext do liftMetaFinishingTactic (grind · declName)
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
