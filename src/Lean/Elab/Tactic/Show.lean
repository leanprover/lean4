/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
prelude
import Lean.Elab.Tactic.Change

namespace Lean.Elab.Tactic
open Meta
/-!
# Implementation of the `show` tactic
-/

def elabShow (newType : Term) : TacticM Unit := do
  let goals ← getGoals
  go newType goals []
where
  go (newType : Term) (l : List MVarId) (prev : List MVarId) : TacticM Unit := do
    match l with
    | [] => throwError "tactic 'show' failed, no goal unifies"
    | goal :: goals =>
      if goals.isEmpty then
        -- optimization for last goal
        try
          tryGoal newType goal goals prev
        catch _ =>
          throwError "tactic 'show' failed, no goal unifies"
      else
        let mstate ← getThe Meta.State
        let info ← getInfoState
        try
          tryGoal newType goal goals prev
        catch _ =>
          -- we might otherwise have multiple instances of term elab information
          setInfoState info
          set mstate
          go newType goals (goal :: prev)
  tryGoal (newType : Term) (goal : MVarId) (l : List MVarId) (prev : List MVarId) : TacticM Unit := do
    let type ← goal.getType
    let tag ← goal.getTag
    let (tgt', mvars) ← goal.withContext
      (withCollectingNewGoalsFrom (elabChange type newType) tag `show)
    let goal' ← goal.replaceTargetDefEq tgt'
    let newGoals := goal' :: prev.reverseAux (mvars ++ l)
    setGoals newGoals

@[builtin_tactic «show»] elab_rules : tactic
  | `(tactic| show $newType:term) => elabShow newType

end Lean.Elab.Tactic
