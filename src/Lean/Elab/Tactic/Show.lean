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
  let (goal :: goals) ← getGoals | throwNoGoalsToBeSolved
  go newType goal goals []
where
  go (newType : Term) (goal : MVarId) (l : List MVarId) (prev : List MVarId) : TacticM Unit := do
    match l with
    | [] => -- last goal
      Tactic.tryCatch
        (tryGoal newType goal [] prev)
        (fun e => throwNestedTacticEx `show e)
    | x :: l' =>
      let state ← saveState
      Tactic.tryCatch (tryGoal newType goal l prev) fun _ => do
        state.restore true
        go newType x l' (goal :: prev)
  tryGoal (newType : Term) (goal : MVarId) (l : List MVarId) (prev : List MVarId) : TacticM Unit := do
    let type ← goal.getType
    let tag ← goal.getTag
    goal.withContext do
      let (tgt', mvars) ← withCollectingNewGoalsFrom (elabChange type newType) tag `show
      let goal' ← goal.replaceTargetDefEq tgt'
      let newGoals := goal' :: prev.reverseAux (mvars ++ l)
      setGoals newGoals

@[builtin_tactic «show»] elab_rules : tactic
  | `(tactic| show $newType:term) => elabShow newType

end Lean.Elab.Tactic
