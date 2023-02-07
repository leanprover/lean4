/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Calc
import Lean.Elab.Tactic.ElabTerm

namespace Lean.Elab.Tactic
open Meta

/-- Elaborator for the `calc` tactic mode variant. -/
@[builtin_tactic calcTactic]
def evalCalc : Tactic := fun stx => withMainContext do
  let steps : TSyntax ``calcSteps := ⟨stx[1]⟩
  let (val, mvarIds) ← withCollectingNewGoalsFrom (tagSuffix := `calc) do
    let target ← getMainTarget
    let tag ← getMainTag
    runTermElab do
    let mut val ← Term.elabCalcSteps steps
    let mut valType ← inferType val
    unless (← isDefEq valType target) do
      let rec throwFailed :=
        throwError "'calc' tactic failed, has type{indentExpr valType}\nbut it is expected to have type{indentExpr target}"
      let some (_, _, rhs) ← Term.getCalcRelation? valType | throwFailed
      let some (r, _, rhs') ← Term.getCalcRelation? target | throwFailed
      let lastStep := mkApp2 r rhs rhs'
      let lastStepGoal ← mkFreshExprSyntheticOpaqueMVar lastStep (tag := tag ++ `calc.step)
      (val, valType) ← Term.mkCalcTrans val valType lastStepGoal lastStep
      unless (← isDefEq valType target) do throwFailed
    return val
  (← getMainGoal).assign val
  replaceMainGoal mvarIds
