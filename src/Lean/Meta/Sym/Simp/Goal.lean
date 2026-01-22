/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
import Lean.Meta.Tactic.Util
import Lean.Meta.AppBuilder
import Lean.Meta.Sym.InferType
namespace Lean.Meta.Sym
/-!
# Goal simplification

Applies `Sym.simp` to a goal's target type, producing a simplified goal or closing it if
the result is `True`.
-/

/-- Result of simplifying a goal with `Sym.simp`. -/
public inductive SimpGoalResult where
  /-- No simplification was possible. -/
  | noProgress
  /-- The goal was closed (simplified to `True`). -/
  | closed
  /-- The goal was simplified to a new goal. -/
  | goal (mvarId : MVarId)

/--
Converts a `SimpGoalResult` to an optional goal.
Returns `none` if closed, `some mvarId` if simplified, or throws an error if no progress.
-/
public def SimpGoalResult.toOption : SimpGoalResult → CoreM (Option MVarId)
  | .noProgress => throwError "`Sym.simp` made no progress "
  | .closed => return none
  | .goal mvarId => return some mvarId

/--
Simplifies the target of `mvarId` using `Sym.simp`.
Returns `.closed` if the target simplifies to `True`, `.simp mvarId'` if simplified
to a new goal, or `.noProgress` if no simplification occurred.

This function assumed the input goal is a valid `Sym` goal (e.g., expressions are maximally shared).
-/
public def simpGoal (mvarId : MVarId) (methods :  Simp.Methods := {}) (config : Simp.Config := {})
    : SymM SimpGoalResult := mvarId.withContext do
  let decl ← mvarId.getDecl
  let target := decl.type
  match (← simp target methods config) with
  | .rfl _ => return .noProgress
  | .step target' h _ =>
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar target' decl.userName
    let u ← getLevel target
    let h := mkApp4 (mkConst ``Eq.mpr [u]) target target' h mvarNew
    mvarId.assign h
    if target'.isTrue then
      mvarNew.mvarId!.assign (mkConst ``True.intro)
      return .closed
    else
      return .goal mvarNew.mvarId!

/--
Similar to `simpGoal`, but returns `.goal mvarId` if no progress was made.
-/
public def trySimpGoal (mvarId : MVarId) (methods :  Simp.Methods := {}) (config : Simp.Config := {})
    : SymM SimpGoalResult := do
  match (← simpGoal mvarId methods config) with
  | .noProgress => return .goal mvarId
  | r => return r

end Lean.Meta.Sym
