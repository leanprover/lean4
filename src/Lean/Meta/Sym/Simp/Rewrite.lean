/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.Simproc
public import Lean.Meta.Sym.Simp.Theorems
public import Lean.Meta.Sym.Simp.App
public import Lean.Meta.Sym.Simp.Discharger
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InstantiateMVarsS
import Init.Data.Range.Polymorphic.Iterators
namespace Lean.Meta.Sym.Simp
open Grind

/--
Creates proof term for a rewriting step.
Handles both constant expressions (common case, avoids `instantiateLevelParams`)
and general expressions.
-/
def mkValue (expr : Expr) (pattern : Pattern) (us : List Level) (args : Array Expr) : Expr :=
  if let .const declName [] := expr then
    mkAppN (mkConst declName us) args
  else
    mkAppN (expr.instantiateLevelParams pattern.levelParams us) args

/--
Tries to rewrite `e` using the given theorem.
-/
public def Theorem.rewrite (thm : Theorem) (e : Expr) (d : Discharger := dischargeNone) : SimpM Result :=
  /-
  **Note**: We use `withNewMCtxDepth` to ensure auxiliary metavariables used during the `match?`
  do not pollute the metavariable context.
  Thus, we must ensure that all assigned variables have be instantiate.
  -/
  withNewMCtxDepth do
  if let some result ← thm.pattern.match? e then
    -- **Note**: Potential optimization: check whether pattern covers all variables.
    let mut args := result.args.toVector
    let us ← result.us.mapM instantiateLevelMVars
    for h : i in *...args.size do
      let arg := args[i]
      if let .mvar mvarId := arg then
        if (← mvarId.isAssigned) then
          let arg ← instantiateMVarsS arg
          args := args.set i arg
        else
          let decl ← mvarId.getDecl
          if let some val ← d decl.type then
            let val ← instantiateMVarsS val
            mvarId.assign val
            args := args.set i val
          else
            -- **Note**: Failed to discharge hypothesis.
            return .rfl
      else if arg.hasMVar then
        let arg ← instantiateMVarsS arg
        args := args.set i arg
    let proof := mkValue thm.expr thm.pattern us args.toArray
    let rhs   := thm.rhs.instantiateLevelParams thm.pattern.levelParams us
    let rhs   ← share rhs
    let expr  ← instantiateRevBetaS rhs args.toArray
    if isSameExpr e expr then
      return .rfl
    else
      return .step expr proof
  else
    return .rfl

public def Theorems.rewrite (thms : Theorems) (d : Discharger := dischargeNone) : Simproc := fun e => do
  for (thm, numExtra) in thms.getMatchWithExtra e do
    let result ← if numExtra == 0 then
      thm.rewrite e d
    else
      simpOverApplied e numExtra (thm.rewrite · d)
    if !result.isRfl then
      return result
  return .rfl

end Lean.Meta.Sym.Simp
