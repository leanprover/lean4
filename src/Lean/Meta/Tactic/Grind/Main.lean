/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Grind.Lemmas
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.ExposeNames
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
  let (bfalseExpr, scState) := ShareCommon.State.shareCommon scState (mkConst ``Bool.false)
  let (btrueExpr, scState)  := ShareCommon.State.shareCommon scState (mkConst ``Bool.true)
  let (natZExpr, scState)  := ShareCommon.State.shareCommon scState (mkNatLit 0)
  let simprocs := params.normProcs
  let simp := params.norm
  let config := params.config
  x (← mkMethods fallback).toMethodsRef { mainDeclName, config, simprocs, simp }
    |>.run' { scState, trueExpr, falseExpr, natZExpr, btrueExpr, bfalseExpr }

private def mkCleanState (mvarId : MVarId) (params : Params) : MetaM Clean.State := mvarId.withContext do
  unless params.config.clean do return {}
  let mut used : PHashSet Name := {}
  for localDecl in (← getLCtx) do
    used := used.insert localDecl.userName
  return { used }

private def mkGoal (mvarId : MVarId) (params : Params) : GrindM Goal := do
  let mvarId ← if params.config.clean then mvarId.exposeNames else pure mvarId
  let trueExpr ← getTrueExpr
  let falseExpr ← getFalseExpr
  let btrueExpr ← getBoolTrueExpr
  let bfalseExpr ← getBoolFalseExpr
  let natZeroExpr ← getNatZeroExpr
  let thmMap := params.ematch
  let casesTypes := params.casesTypes
  let clean ← mkCleanState mvarId params
  GoalM.run' { mvarId, ematch.thmMap := thmMap, split.casesTypes := casesTypes, clean } do
    mkENodeCore falseExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore trueExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore btrueExpr (interpreted := false) (ctor := true) (generation := 0)
    mkENodeCore bfalseExpr (interpreted := false) (ctor := true) (generation := 0)
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
  trace    : Trace
  counters : Counters

private def countersToMessageData (header : String) (cls : Name) (data : Array (Name × Nat)) : MetaM MessageData := do
  let data := data.qsort fun (d₁, c₁) (d₂, c₂) => if c₁ == c₂ then Name.lt d₁ d₂ else c₁ > c₂
  let data ← data.mapM fun (declName, counter) =>
    return .trace { cls } m!"{.ofConst (← mkConstWithLevelParams declName)} ↦ {counter}" #[]
  return .trace { cls } header data

def Counters.toMessageData? (cs : Counters) : MetaM (Option MessageData) := do
  let thms := cs.thm.toList.toArray.filterMap fun (origin, c) =>
    match origin with
    | .decl declName => some (declName, c)
    | _ => none
  -- We do not report `cases` applications on builtin types
  let cases := cs.case.toList.toArray.filter fun (declName, _) => !isBuiltinEagerCases declName
  let mut msgs := #[]
  unless thms.isEmpty do
    msgs := msgs.push <| (← countersToMessageData "E-Matching instances" `thm thms)
  unless cases.isEmpty do
    msgs := msgs.push <| (← countersToMessageData "Cases instances" `cases cases)
  if msgs.isEmpty then
    return none
  else
    return some <| .trace { cls := `grind } "Counters" msgs

def Result.hasFailures (r : Result) : Bool :=
  !r.failures.isEmpty

def Result.toMessageData (result : Result) : MetaM MessageData := do
  let mut msgs ← result.failures.mapM (goalToMessageData · result.config)
  if result.config.verbose then
    let mut issues := result.issues
    unless result.skipped.isEmpty do
      let m := m!"#{result.skipped.length} other goal(s) were not fully processed due to previous failures, threshold: `(failures := {result.config.failures})`"
      issues := .trace { cls := `issue } m #[] :: issues
    unless issues.isEmpty do
      msgs := msgs ++ [.trace { cls := `grind } "Issues" issues.reverse.toArray]
    if let some msg ← result.counters.toMessageData? then
      msgs := msgs ++ [msg]
  return MessageData.joinSep msgs m!"\n"

def main (mvarId : MVarId) (params : Params) (mainDeclName : Name) (fallback : Fallback) : MetaM Result := do profileitM Exception "grind" (← getOptions) do
  let go : GrindM Result := do
    let goals ← initCore mvarId params
    let (failures, skipped) ← solve goals fallback
    trace[grind.debug.final] "{← ppGoals goals}"
    let issues   := (← get).issues
    let trace    := (← get).trace
    let counters := (← get).counters
    if failures.isEmpty then
      -- If there are no failures and diagnostics are enabled, we still report the performance counters.
      if (← isDiagnosticsEnabled) then
        if let some msg ← counters.toMessageData? then
          logInfo msg
    return { failures, skipped, issues, config := params.config, trace, counters }
  go.run mainDeclName params fallback

end Lean.Meta.Grind
