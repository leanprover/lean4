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
Instantiates the assigned metavariable at the head of `e` and beta-reduces. The arguments keep
their metavariables.
-/
public partial def instantiateMVarsIfMVarAppS (e : Expr) : SymM Expr := do
  let .mvar mvarId := e.getAppFn | return e
  let some v ← getExprMVarAssignment? mvarId | return e
  instantiateMVarsIfMVarAppS (← betaS (← shareCommon v) e.getAppArgs)

end Lean.Meta.Sym
