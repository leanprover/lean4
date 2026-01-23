/-
Copyright (c) 2026 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Simp.Discharger
import Lean.Meta.Sym.Simp.Theorems
import Lean.Meta.Sym.Simp.Rewrite
import Lean.Meta.Sym.Simp.EvalGround
import Lean.Meta.Sym.Simp.Goal
import Lean.Meta.Sym.Simp.ControlFlow
import Lean.Meta.Sym.Util
import Lean.Meta.Tactic.Util
import Lean.Meta.AppBuilder
import Lean.Meta.Sym.LitValues
import Lean.Meta.Match.MatcherInfo
namespace Lean.Meta.Sym
open Simp
/-!
Helper functions for debugging purposes and creating tests.
-/

public def mkSimprocFor (declNames : Array Name) (d : Discharger := dischargeNone) : MetaM Simproc := do
  let mut thms : Theorems := {}
  for declName in declNames do
    thms := thms.insert (← mkTheoremFromDecl declName)
  return thms.rewrite d

public def isValue : Simproc := fun e => do
  if (←(getNatValue? e).run).isSome then
    return .rfl (done := true)
  else
    return .rfl

public def unfoldSimproc : Simproc := fun e => do
  let fn := e.getAppFn
  if fn.isConst then
    let fnName := fn.constName!
    let matcherInfo ← getMatcherInfo? fnName
    if matcherInfo.isSome then return .rfl
    let some thm ← mkTheoremsFromEquations fnName | return .rfl

    let mut thms : Theorems := {}
    thms := thms.insert thm
    thms.rewrite dischargeNone e
  else
    return .rfl

def skipBinders : Simproc := fun e =>
  if e.isLambda then return .rfl (done := true) else
  if e.isForall then return .rfl (done := true)
  else return .rfl

def cbvPre : Simproc := skipBinders >> simpControl >> evalGround
def cbvPost : Simproc := evalGround >> isValue >> unfoldSimproc

public def mkCbvMethods : MetaM Methods := do
  return {pre := cbvPre, post := cbvPost}

public def runCbv (e : Expr) (config : Simp.Config := {}) : MetaM Result := do
  let methods ← mkCbvMethods
  SymM.run do
    let preprocessed ← preprocessExpr e
    simp preprocessed methods config

public def mkMethods (declNames : Array Name) : MetaM Methods := do
  return { post := (← mkSimprocFor declNames) }

public def simpGoalUsing (declNames : Array Name) (mvarId : MVarId) : MetaM (Option MVarId) := SymM.run do
  let methods ← mkMethods declNames
  let mvarId ← preprocessMVar mvarId
  (← simpGoal mvarId methods).toOption

public def simpGoalUsingCbv (mvarId : MVarId) : MetaM (Option MVarId) := SymM.run do
  let methods ← mkCbvMethods
  let mvarId ← preprocessMVar mvarId
  (← simpGoal mvarId methods).toOption

end Lean.Meta.Sym
