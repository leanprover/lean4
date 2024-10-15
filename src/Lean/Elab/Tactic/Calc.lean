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
      let target := (← instantiateMVars target).consumeMData
      let (val, mvarIds) ← withCollectingNewGoalsFrom (parentTag := tag) (tagSuffix := `calc) <| runTermElab do
        let elhs? := (← Term.getCalcRelation? target).map (fun (_, lhs, _) => lhs)
        -- We can't elaborate with an expected RHS because of the last-step-extension feature below
        let (val, valType) ← Term.elabCalcSteps steps (expectedLhs? := elhs?)
        if (← isDefEq valType target) then
          return val

        let some (_, _, rhs) ← Term.getCalcRelation? valType | unreachable!
        let some (r, elhs, erhs) ← Term.getCalcRelation? target
          | throwError "'calc' tactic failed, goal is not a relation{indentExpr target}"

        -- Feature: if the goal is `x ~ y`, try extending the `calc` with `_ ~ y` with a new "last step" goal.
        -- We so far have that the LHSs are the same.
        if (← isDefEq (← inferType rhs) (← inferType elhs)) then
          let lastStep := mkApp2 r rhs erhs
          let lastStepGoal ← mkFreshExprSyntheticOpaqueMVar lastStep (tag := tag ++ `calc.step)
          let (val', valType') ← Term.mkCalcTrans val valType lastStepGoal lastStep
          if (← isDefEq valType' target) then
            return val'

        -- LHSs and RHSs are correct for `valType'`, so transitivity must not have given the expected relation.
        -- Calc extension failed, so let's go back and throw an error relevant to the original `valType`.
        let some (r', _, _) ← Term.getCalcRelation? valType | unreachable!
        if (← isDefEq rhs erhs) then
          Term.throwCalcRelationError r' r
        else
          let `(calcStep| $lastPred := $_) := (← Term.getCalcSteps steps).back | unreachable!
          Term.throwCalcRHSError lastPred rhs erhs
      pushGoals mvarIds
      return val
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
