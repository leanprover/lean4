/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Grind.RevertAll
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Proj
import Lean.Meta.Tactic.Grind.ForallProp
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Inv
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.Split
import Lean.Meta.Tactic.Grind.Solve
import Lean.Meta.Tactic.Grind.SimpUtil

namespace Lean.Meta.Grind

structure Params where
  config    : Grind.Config
  ematch    : EMatchTheorems := {}
  extra     : PArray EMatchTheorem := {}
  norm      : Simp.Context
  normProcs : Array Simprocs
  -- TODO: inductives to split

def mkParams (config : Grind.Config) : MetaM Params := do
  let norm ← Grind.getSimpContext
  let normProcs ← Grind.getSimprocs
  return { config, norm, normProcs }

def mkMethods (fallback : Fallback) : CoreM Methods := do
  let builtinPropagators ← builtinPropagatorsRef.get
  return {
    fallback
    propagateUp := fun e => do
     propagateForallPropUp e
     let .const declName _ := e.getAppFn | return ()
     propagateProjEq e
     if let some prop := builtinPropagators.up[declName]? then
       prop e
    propagateDown := fun e => do
     propagateForallPropDown e
     let .const declName _ := e.getAppFn | return ()
     if let some prop := builtinPropagators.down[declName]? then
       prop e
  }

def GrindM.run (x : GrindM α) (mainDeclName : Name) (params : Params) (fallback : Fallback) : MetaM α := do
  let scState := ShareCommon.State.mk _
  let (falseExpr, scState) := ShareCommon.State.shareCommon scState (mkConst ``False)
  let (trueExpr, scState)  := ShareCommon.State.shareCommon scState (mkConst ``True)
  let (natZExpr, scState)  := ShareCommon.State.shareCommon scState (mkNatLit 0)
  let simprocs := params.normProcs
  let simp := params.norm
  let config := params.config
  x (← mkMethods fallback).toMethodsRef { mainDeclName, config, simprocs, simp } |>.run' { scState, trueExpr, falseExpr, natZExpr }

private def mkGoal (mvarId : MVarId) (params : Params) : GrindM Goal := do
  let trueExpr ← getTrueExpr
  let falseExpr ← getFalseExpr
  let natZeroExpr ← getNatZeroExpr
  let thmMap := params.ematch
  GoalM.run' { mvarId, thmMap } do
    mkENodeCore falseExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore trueExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore natZeroExpr (interpreted := true) (ctor := false) (generation := 0)
    for thm in params.extra do
      activateTheorem thm 0

private def initCore (mvarId : MVarId) (params : Params) : GrindM (List Goal) := do
  mvarId.ensureProp
  -- TODO: abstract metavars
  mvarId.ensureNoMVar
  let mvarId ← mvarId.clearAuxDecls
  let mvarId ← mvarId.revertAll
  let mvarId ← mvarId.unfoldReducible
  let mvarId ← mvarId.betaReduce
  appendTagSuffix mvarId `grind
  let goals ← intros (← mkGoal mvarId params) (generation := 0)
  goals.forM (·.checkInvariants (expensive := true))
  return goals.filter fun goal => !goal.inconsistent

def main (mvarId : MVarId) (params : Params) (mainDeclName : Name) (fallback : Fallback) : MetaM (List Goal) := do
  let go : GrindM (List Goal) := do
    let goals ← initCore mvarId params
    let goals ← solve goals
    let goals ← goals.filterMapM fun goal => do
      if goal.inconsistent then return none
      let goal ← GoalM.run' goal fallback
      if goal.inconsistent then return none
      if (← goal.mvarId.isAssigned) then return none
      return some goal
    trace[grind.debug.final] "{← ppGoals goals}"
    return goals
  go.run mainDeclName params fallback

end Lean.Meta.Grind
