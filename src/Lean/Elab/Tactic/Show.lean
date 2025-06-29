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
  let goals@(goal :: _) ← getGoals | throwNoGoalsToBeSolved
  go newType goal goals []
where
  go (newType : Term) (firstGoal : MVarId) (goals : List MVarId) (prevRev : List MVarId) : TacticM Unit := do
    match goals with
    | [] =>
      -- re-run first goal for error message
      tryGoal newType firstGoal (← getGoals).tail [] manyError
    | goal :: goals =>
      if goals.isEmpty && (prevRev.isEmpty || !(← read).recover) then
        -- optimization for single goal / last goal without error recovery
        tryGoal newType goal goals prevRev simpleError
      else
        /-
        Save state manually to make sure that the info state is reverted,
        since `elabChange` elaborates the pattern each time.
        -/
        let state ← saveState
        Tactic.tryCatch
          (withoutRecover (tryGoal newType goal goals prevRev simpleError))
          fun _ => do
            state.restore true
            go newType firstGoal goals (goal :: prevRev)
  tryGoal (newType : Term) (goal : MVarId) (goals : List MVarId) (prevRev : List MVarId) (err : Expr → Expr → MetaM MessageData) : TacticM Unit := do
    let type ← goal.getType
    let tag ← goal.getTag
    goal.withContext do
      let (tgt', mvars) ← withCollectingNewGoalsFrom
        (elabChange type newType err)
        tag `show
      let goal' ← goal.replaceTargetDefEq tgt'
      let newGoals := goal' :: prevRev.reverseAux (mvars ++ goals)
      setGoals newGoals
  simpleError (p tgt : Expr) : MetaM MessageData := do
    return m!"\
      'show' tactic failed, pattern{indentExpr p}\n\
      is not definitionally equal to target{indentExpr tgt}"
  manyError (p tgt : Expr) : MetaM MessageData := do
    return m!"\
      'show' tactic failed, no goals unify with the given pattern.\n\
      \n\
      In the first goal, the pattern{indentExpr p}\n\
      is not definitionally equal to the target{indentExpr tgt}\n\
      (Errors for other goals omitted)"

@[builtin_tactic «show»] elab_rules : tactic
  | `(tactic| show $newType:term) => elabShow newType

end Lean.Elab.Tactic
