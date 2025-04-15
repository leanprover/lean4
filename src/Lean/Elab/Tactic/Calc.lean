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
          -- Immediately the right type, no need for further processing.
          return val

        let some (_, lhs, rhs) ← Term.getCalcRelation? valType | unreachable!
        if let some (er, elhs, erhs) ← Term.getCalcRelation? target then
          -- Feature: if the goal is `x ~ y`, try extending the `calc` with `_ ~ y` with a new "last step" goal.
          if ← isDefEq lhs elhs <&&> isDefEq (← inferType rhs) (← inferType elhs) then
            let lastStep := mkApp2 er rhs erhs
            let lastStepGoal ← mkFreshExprSyntheticOpaqueMVar lastStep (tag := tag ++ `calc.step)
            try
              let (val', valType') ← Term.mkCalcTrans val valType lastStepGoal lastStep
              if (← isDefEq valType' target) then
                return val'
            catch _ =>
              pure ()

        -- Calc extension failed, so let's go back and mimic the `calc` expression
        Term.ensureHasTypeWithErrorMsgs target val
          (mkImmedErrorMsg := fun _ => Term.throwCalcFailure steps)
          (mkErrorMsg := fun _ => Term.throwCalcFailure steps)
      pushGoals mvarIds
      return val
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
