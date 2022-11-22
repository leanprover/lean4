/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.Calc
import Lean.Elab.Tactic.ElabTerm

namespace Lean.Elab.Tactic
open Meta

def elabCalcSteps (steps : Array Syntax) : TacticM Expr := do
  /- If error recovery is disabled, we disable `Term.withoutErrToSorry` -/
  if (← read).recover then
    go
  else
    Term.withoutErrToSorry go
where
  go : TermElabM Expr := do
    let e ← Term.elabCalcSteps steps
    Term.synthesizeSyntheticMVars (mayPostpone := false)
    instantiateMVars e

/-- Elaborator for the `calc` tactic mode variant. -/
@[builtin_tactic calcTactic]
def evalCalc : Tactic := fun stx => do
  withMainContext do
    let steps := #[stx[1]] ++ stx[2].getArgs
    let (val, mvarIds) ← withCollectingNewGoalsFrom (tagSuffix := `calc) do
      let val ← elabCalcSteps steps
      let valType ← inferType val
      let target ← getMainTarget
      if (← isDefEq valType target) then
        return val
      else
        let throwFailed {α} : TacticM α :=
          throwError "'calc' tactic failed, has type{indentExpr valType}\nbut it is expected to have type{indentExpr target}"
        let some (_, _, rhs) ← Term.getCalcRelation? valType | throwFailed
        let some (r, _, rhs') ← Term.getCalcRelation? target | throwFailed
        let lastStep := mkApp2 r rhs rhs'
        let lastStepGoal ← mkFreshExprSyntheticOpaqueMVar lastStep (tag := (← getMainTag) ++ `calc.step)
        let (val, valType) ← Term.mkCalcTrans val valType lastStepGoal lastStep
        unless (← isDefEq valType target) do throwFailed
        return val
    let val ← instantiateMVars val
    let mvarId ← getMainGoal
    mvarId.assign val
    replaceMainGoal mvarIds
