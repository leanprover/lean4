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

The `show p` tactic finds the first goal that `p` unifies with and brings it to the front of the
goal list. If there were a `first_goal` combinator, it would be like `first_goal change p`.
-/

def elabShow (newType : Term) : TacticM Unit := do
  let (goal :: goals) ← getGoals | throwNoGoalsToBeSolved
  go newType goal goals []
where
  go (newType : Term) (goal : MVarId) (goals : List MVarId) (prevRev : List MVarId) : TacticM Unit := do
    match goals with
    | [] => tryGoal newType goal [] prevRev -- last goal
    | x :: l' =>
      /-
      Save state manually to make sure that the info state is reverted,
      since `elabChange` elaborates the pattern each time.
      -/
      let state ← saveState
      Tactic.tryCatch
        (withoutRecover (tryGoal newType goal goals prevRev))
        fun _ => do
          state.restore true
          go newType x l' (goal :: goals)
  tryGoal (newType : Term) (goal : MVarId) (goals : List MVarId) (prevRev : List MVarId) : TacticM Unit := do
    let type ← goal.getType
    let tag ← goal.getTag
    goal.withContext do
      let (tgt', mvars) ← withCollectingNewGoalsFrom (elabChange type newType `show) tag `show
      let goal' ← goal.replaceTargetDefEq tgt'
      let newGoals := goal' :: prevRev.reverseAux (mvars ++ goals)
      setGoals newGoals

@[builtin_tactic «show»] elab_rules : tactic
  | `(tactic| show $newType:term) => elabShow newType

end Lean.Elab.Tactic
