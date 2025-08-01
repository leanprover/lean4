/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Init.Grind.Lemmas
public import Lean.Meta.Tactic.Util
public import Lean.Meta.Tactic.ExposeNames
public import Lean.Meta.Tactic.Simp.Diagnostics
public import Lean.Meta.Tactic.Grind.Split  -- TODO: not minimal yet
import Lean.Meta.Tactic.Grind.RevertAll
import Lean.Meta.Tactic.Grind.PropagatorAttr
import Lean.Meta.Tactic.Grind.Proj
import Lean.Meta.Tactic.Grind.ForallProp
import Lean.Meta.Tactic.Grind.Util
import Lean.Meta.Tactic.Grind.Inv
import Lean.Meta.Tactic.Grind.Intro
import Lean.Meta.Tactic.Grind.EMatch
import Lean.Meta.Tactic.Grind.Solve
import Lean.Meta.Tactic.Grind.SimpUtil
import Lean.Meta.Tactic.Grind.Cases
import Lean.Meta.Tactic.Grind.LawfulEqCmp
import Lean.Meta.Tactic.Grind.ReflCmp

public section

namespace Lean.Meta.Grind

structure Params where
  config     : Grind.Config
  ematch     : EMatchTheorems := default
  symPrios   : SymbolPriorities := {}
  casesTypes : CasesTypes := {}
  extra      : PArray EMatchTheorem := {}
  norm       : Simp.Context
  normProcs  : Array Simprocs
  -- TODO: inductives to split

def mkParams (config : Grind.Config) : MetaM Params := do
  let norm ← Grind.getSimpContext config
  let normProcs ← Grind.getSimprocs
  let symPrios ← getGlobalSymbolPriorities
  return { config, norm, normProcs, symPrios }

def mkMethods (fallback : Fallback) : CoreM Methods := do
  let builtinPropagators ← builtinPropagatorsRef.get
  return {
    fallback
    propagateUp := fun e => do
     propagateForallPropUp e
     propagateReflCmp e
     let .const declName _ := e.getAppFn | return ()
     propagateProjEq e
     if let some prop := builtinPropagators.up[declName]? then
       prop e
    propagateDown := fun e => do
     propagateForallPropDown e
     propagateLawfulEqCmp e
     let .const declName _ := e.getAppFn | return ()
     if let some prop := builtinPropagators.down[declName]? then
       prop e
  }

-- A `simp` discharger that does not use assumptions.
-- We use it to make sure we don't have to reset the `simp` cache used in `grind`.
private def discharge? (e : Expr) : SimpM (Option Expr) := do
  let e := e.cleanupAnnotations
  let r ← Simp.simp e
  if let some p ← Simp.dischargeRfl r.expr then
    return some (mkApp4 (mkConst ``Eq.mpr [levelZero]) e r.expr (← r.getProof) p)
  else if r.expr.isTrue then
    return some (← mkOfEqTrue (← r.getProof))
  else
    return none

def GrindM.run (x : GrindM α) (params : Params) (fallback : Fallback) : MetaM α := do
  let (falseExpr, scState)  := shareCommonAlpha (mkConst ``False) {}
  let (trueExpr, scState)   := shareCommonAlpha (mkConst ``True) scState
  let (bfalseExpr, scState) := shareCommonAlpha (mkConst ``Bool.false) scState
  let (btrueExpr, scState)  := shareCommonAlpha (mkConst ``Bool.true) scState
  let (natZExpr, scState)   := shareCommonAlpha (mkNatLit 0) scState
  let (ordEqExpr, scState)  := shareCommonAlpha (mkConst ``Ordering.eq) scState
  let (intExpr, scState)    := shareCommonAlpha Int.mkType scState
  let simprocs := params.normProcs
  let simpMethods := Simp.mkMethods simprocs discharge? (wellBehavedDischarge := true)
  let simp := params.norm
  let config := params.config
  let symPrios := params.symPrios
  x (← mkMethods fallback).toMethodsRef { config, simpMethods, simp, trueExpr, falseExpr, natZExpr, btrueExpr, bfalseExpr, ordEqExpr, intExpr, symPrios }
    |>.run' { scState }

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
  let ordEqExpr ← getOrderingEqExpr
  let thmMap := params.ematch
  let casesTypes := params.casesTypes
  let clean ← mkCleanState mvarId params
  GoalM.run' { mvarId, ematch.thmMap := thmMap, split.casesTypes := casesTypes, clean } do
    mkENodeCore falseExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore trueExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore btrueExpr (interpreted := false) (ctor := true) (generation := 0)
    mkENodeCore bfalseExpr (interpreted := false) (ctor := true) (generation := 0)
    mkENodeCore natZeroExpr (interpreted := true) (ctor := false) (generation := 0)
    mkENodeCore ordEqExpr (interpreted := false) (ctor := true) (generation := 0)
    for thm in params.extra do
      activateTheorem thm 0

structure Result where
  failure?   : Option Goal
  issues     : List MessageData
  config     : Grind.Config
  trace      : Trace
  counters   : Counters
  simp       : Simp.Stats
  splitDiags : PArray SplitDiagInfo

private def countersToMessageData (header : String) (cls : Name) (data : Array (Name × Nat)) : MetaM MessageData := do
  let data := data.qsort fun (d₁, c₁) (d₂, c₂) => if c₁ == c₂ then Name.lt d₁ d₂ else c₁ > c₂
  let data ← data.mapM fun (declName, counter) =>
    return .trace { cls } m!"{.ofConst (← mkConstWithLevelParams declName)} ↦ {counter}" #[]
  return .trace { cls } header data

private def splitDiagInfoToMessageData (ss : Array SplitDiagInfo) : MetaM MessageData := do
  let env  ← getEnv
  let mctx ← getMCtx
  let opts ← getOptions
  let cls := `split
  let data ← ss.mapM fun { c, lctx, numCases, gen, splitSource } => do
    let header := m!"{c}"
    return MessageData.withContext { env, mctx, lctx, opts } <| .trace { cls } header #[
      .trace { cls } m!"source: {← splitSource.toMessageData}" #[],
      .trace { cls } m!"generation: {gen}" #[],
      .trace { cls } m!"# cases: {numCases}" #[]
    ]
  return .trace { cls } "Case splits" data

-- Diagnostics information for the whole search
private def mkGlobalDiag (cs : Counters) (simp : Simp.Stats) (ss : PArray SplitDiagInfo) : MetaM (Option MessageData) := do
  let thms := cs.thm.toList.toArray.filterMap fun (origin, c) =>
    match origin with
    | .decl declName => some (declName, c)
    | _ => none
  -- We do not report `cases` applications on builtin types
  let cases := cs.case.toList.toArray.filter fun (declName, _) => !isBuiltinEagerCases declName
  let mut msgs := #[]
  unless thms.isEmpty do
    msgs := msgs.push <| (← countersToMessageData "E-Matching instances" `thm thms)
  let ss := ss.toArray.filter fun { numCases, .. } => numCases > 1
  unless ss.isEmpty do
    msgs := msgs.push <| (← splitDiagInfoToMessageData ss)
  unless cases.isEmpty do
    msgs := msgs.push <| (← countersToMessageData "Cases instances" `cases cases)
  unless cs.apps.isEmpty do
    msgs := msgs.push <| (← countersToMessageData "Applications" `app cs.apps.toList.toArray)
  let simpMsgs ← Simp.mkDiagMessages simp.diag
  unless simpMsgs.isEmpty do
    msgs := msgs.push <| .trace { cls := `grind} "Simplifier" simpMsgs
  if msgs.isEmpty then
    return none
  else
    return some <| .trace { cls := `grind } "Diagnostics" msgs

def Result.hasFailed (r : Result) : Bool :=
  r.failure?.isSome

def Result.toMessageData (result : Result) : MetaM MessageData := do
  let mut msgs ← result.failure?.toList.mapM (goalToMessageData · result.config)
  if result.config.verbose then
    let mut issues := result.issues
    -- We did not find the following very useful in practice.
    /-
    unless result.skipped.isEmpty do
      let m := m!"#{result.skipped.length} other goal(s) were not fully processed due to previous failures, threshold: `(failures := {result.config.failures})`"
      issues := .trace { cls := `issue } m #[] :: issues
    -/
    unless issues.isEmpty do
      msgs := msgs ++ [.trace { cls := `grind } "Issues" issues.reverse.toArray]
    if let some msg ← mkGlobalDiag result.counters result.simp result.splitDiags then
      msgs := msgs ++ [msg]
  return MessageData.joinSep msgs m!"\n"

private def initCore (mvarId : MVarId) (params : Params) : GrindM Goal := do
  let mvarId ← mvarId.abstractMVars
  let mvarId ← mvarId.clearAuxDecls
  let mvarId ← mvarId.revertAll
  let mvarId ← mvarId.unfoldReducible
  let mvarId ← mvarId.betaReduce
  appendTagSuffix mvarId `grind
  mkGoal mvarId params

def main (mvarId : MVarId) (params : Params) (fallback : Fallback) : MetaM Result := do profileitM Exception "grind" (← getOptions) do
  if debug.terminalTacticsAsSorry.get (← getOptions) then
    mvarId.admit
    return {
        failure? := none, issues := [], config := params.config, trace := {}, counters := {}, simp := {}, splitDiags := {}
    }
  let go : GrindM Result := withReducible do
    let goal       ← initCore mvarId params
    let failure?   ← solve goal
    let issues     := (← get).issues
    let trace      := (← get).trace
    let counters   := (← get).counters
    let splitDiags := (← get).splitDiags
    let simp       := { (← get).simp with }
    if failure?.isNone then
      -- If there are no failures and diagnostics are enabled, we still report the performance counters.
      if (← isDiagnosticsEnabled) then
        if let some msg ← mkGlobalDiag counters simp splitDiags then
          logInfo msg
    return { failure?, issues, config := params.config, trace, counters, simp, splitDiags }
  go.run params fallback

end Lean.Meta.Grind
