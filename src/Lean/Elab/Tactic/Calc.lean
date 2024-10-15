/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Calc
import Lean.Elab.Tactic.ElabTerm

namespace Lean.Elab.Tactic
open Meta

/-- Elaborator for the `calc` tactic mode variant. -/
@[builtin_tactic Lean.calcTactic]
def evalCalc : Tactic
  | `(tactic| calc%$tk $steps:calcSteps) =>
    withRef tk do
    closeMainGoalUsing `calc (checkNewUnassigned := false) fun target tag => do
    withTacticInfoContext steps do
      let steps ← Term.mkCalcStepViews steps
      let target := (← instantiateMVars target).consumeMData
      let (val, mvarIds) ← withCollectingNewGoalsFrom (parentTag := tag) (tagSuffix := `calc) <| runTermElab do
        let (val, valType) ← Term.elabCalcSteps steps
        if (← isDefEq valType target) then
          return val

        let some (_, lhs, rhs) ← Term.getCalcRelation? valType | unreachable!
        let some (er, elhs, erhs) ← Term.getCalcRelation? target
          | throwError "'calc' tactic failed, goal is not a relation{indentExpr target}"

        -- Feature: if the goal is `x ~ y`, try extending the `calc` with `_ ~ y` with a new "last step" goal.
        -- We so far have that the LHSs are the same.
        if ← isDefEq lhs elhs <&&> isDefEq (← inferType rhs) (← inferType elhs) then
          let lastStep := mkApp2 er rhs erhs
          let lastStepGoal ← mkFreshExprSyntheticOpaqueMVar lastStep (tag := tag ++ `calc.step)
          let (val', valType') ← Term.mkCalcTrans val valType lastStepGoal lastStep
          if (← isDefEq valType' target) then
            return val'

        -- Calc extension failed, so let's go back and throw an error relevant to the original `valType`.
        Term.throwCalcFailure steps target valType val
      pushGoals mvarIds
      return val
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
