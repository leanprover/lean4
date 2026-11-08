/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.SymM
import Lean.Meta.Sym.InstantiateS
namespace Lean.Meta.Sym

/--
Instantiates metavariables occurring in `e`, and returns a maximally shared term.
-/
public def instantiateMVarsS (e : Expr) : SymM Expr := do
  if e.hasMVar then
    -- **Note**: If this is a bottleneck, write a new function that combines both steps.
    shareCommon (← instantiateMVars e)
  else
    return e

/--
Head-only variant of `instantiateMVarsS`: instantiates and reshares only when the head of `e` is a
metavariable, otherwise returns `e` unchanged.
-/
public def instantiateMVarsIfMVarAppS (e : Expr) : SymM Expr := do
  if e.getAppFn.isMVar then
    instantiateMVarsS e
  else
    return e

/--
If the head of `e` is a metavariable that `instantiateMVars` replaces, returns `e` with the head
replaced by its value and beta-reduced, and `none` otherwise. The arguments of `e` are not
traversed.
-/
public def instantiateAssignedMVarHeadS? (e : Expr) : SymM (Option Expr) := do
  let .mvar mvarId := e.getAppFn | return none
  if let some val ← getExprMVarAssignment? mvarId then
    -- `val` may not be maximally shared, e.g., when assigned by `isDefEq`.
    let val ← instantiateMVarsS val
    return some (← betaS val e.getAppArgs)
  let some { fvars, mvarIdPending } ← getDelayedMVarAssignment? mvarId | return none
  let args := e.getAppArgs
  if args.size < fvars.size then return none
  let val ← instantiateMVars (mkMVar mvarIdPending)
  if val.hasExprMVar then return none
  let val ← shareCommon (val.abstract fvars)
  let val ← instantiateRevRangeS val 0 fvars.size args
  return some (← betaS val (args.extract fvars.size args.size))

end Lean.Meta.Sym
