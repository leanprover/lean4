/-
Copyright (c) 2022 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kim Morrison
-/
prelude
import Lean.Meta.Tactic.Repeat
import Lean.Elab.Tactic.Basic

namespace Lean.Elab.Tactic

@[builtin_tactic repeat']
def evalRepeat' : Tactic := fun stx => do
  match stx with
  | `(tactic| repeat' $tac:tacticSeq) =>
     setGoals (← Meta.repeat' (evalTacticAtRaw tac) (← getGoals))
  | _ => throwUnsupportedSyntax

@[builtin_tactic repeat1']
def evalRepeat1' : Tactic := fun stx => do
  match stx with
  | `(tactic| repeat1' $tac:tacticSeq) =>
    setGoals (← Meta.repeat1' (evalTacticAtRaw tac) (← getGoals))
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
