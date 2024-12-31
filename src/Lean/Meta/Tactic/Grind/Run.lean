/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Grind.Types
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Proj

namespace Lean.Meta.Grind

def mkMethods : CoreM Methods := do
  let builtinPropagators ← builtinPropagatorsRef.get
  return {
    propagateUp := fun e => do
     let .const declName _ := e.getAppFn | return ()
     propagateProjEq e
     if let some prop := builtinPropagators.up[declName]? then
       prop e
    propagateDown := fun e => do
     let .const declName _ := e.getAppFn | return ()
     if let some prop := builtinPropagators.down[declName]? then
       prop e
  }

def GrindM.run (x : GrindM α) (mainDeclName : Name) (config : Grind.Config) : MetaM α := do
  let scState := ShareCommon.State.mk _
  let (falseExpr, scState) := ShareCommon.State.shareCommon scState (mkConst ``False)
  let (trueExpr, scState)  := ShareCommon.State.shareCommon scState (mkConst ``True)
  let thms ← grindNormExt.getTheorems
  let simprocs := #[(← grindNormSimprocExt.getSimprocs)]
  let simp ← Simp.mkContext
    (config := { arith := true })
    (simpTheorems := #[thms])
    (congrTheorems := (← getSimpCongrTheorems))
  x (← mkMethods).toMethodsRef { mainDeclName, config, simprocs, simp } |>.run' { scState, trueExpr, falseExpr }

@[inline] def GoalM.run (goal : Goal) (x : GoalM α) : GrindM (α × Goal) :=
  goal.mvarId.withContext do StateRefT'.run x goal

@[inline] def GoalM.run' (goal : Goal) (x : GoalM Unit) : GrindM Goal :=
  goal.mvarId.withContext do StateRefT'.run' (x *> get) goal

def mkGoal (mvarId : MVarId) : GrindM Goal := do
  let trueExpr ← getTrueExpr
  let falseExpr ← getFalseExpr
  let thmMap ← getEMatchTheorems
  GoalM.run' { mvarId, thmMap } do
    mkENodeCore falseExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore trueExpr (interpreted := true) (ctor := false) (generation := 0)

end Lean.Meta.Grind
