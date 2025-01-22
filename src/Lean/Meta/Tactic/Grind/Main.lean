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
import Lean.Meta.Tactic.Grind.Cases

namespace Lean.Meta.Grind

structure Params where
  config     : Grind.Config
  ematch     : EMatchTheorems := {}
  casesTypes : CasesTypes := {}
  extra      : PArray EMatchTheorem := {}
  norm       : Simp.Context
  normProcs  : Array Simprocs
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
  let casesTypes := params.casesTypes
  GoalM.run' { mvarId, thmMap, casesTypes } do
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

structure Result where
  failures : List Goal
  skipped  : List Goal
  issues   : List MessageData
  config   : Grind.Config

def Result.hasFailures (r : Result) : Bool :=
  !r.failures.isEmpty

def Result.toMessageData (result : Result) : MetaM MessageData := do
  let mut msgs ← result.failures.mapM (goalToMessageData · result.config)
  let mut issues := result.issues
  unless result.skipped.isEmpty do
    let m := m!"#{result.skipped.length} other goal(s) were not fully processed due to previous failures, threshold: `(failures := {result.config.failures})`"
    issues := .trace { cls := `issue } m #[] :: issues
  unless issues.isEmpty do
    msgs := msgs ++ [.trace { cls := `grind } "Issues" issues.reverse.toArray]
  return MessageData.joinSep msgs m!"\n"

def main (mvarId : MVarId) (params : Params) (mainDeclName : Name) (fallback : Fallback) : MetaM Result := do
  let go : GrindM Result := do
    let goals ← initCore mvarId params
    let (failures, skipped) ← solve goals fallback
    trace[grind.debug.final] "{← ppGoals goals}"
    let issues := (← get).issues
    return { failures, skipped, issues, config := params.config }
  go.run mainDeclName params fallback

end Lean.Meta.Grind
