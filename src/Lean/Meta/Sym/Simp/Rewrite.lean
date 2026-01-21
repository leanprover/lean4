/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module
prelude
public import Lean.Meta.Sym.Simp.SimpM
public import Lean.Meta.Sym.Simp.Simproc
public import Lean.Meta.Sym.Simp.Theorems
public import Lean.Meta.Sym.Simp.App
public import Lean.Meta.Sym.Simp.Discharger
import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.Simp.DiscrTree
namespace Lean.Meta.Sym.Simp
open Grind

/--
Creates proof term for a rewriting step.
Handles both constant expressions (common case, avoids `instantiateLevelParams`)
and general expressions.
-/
def mkValue (expr : Expr) (pattern : Pattern) (result : MatchUnifyResult) : Expr :=
  if let .const declName [] := expr then
    mkAppN (mkConst declName result.us) result.args
  else
    mkAppN (expr.instantiateLevelParams pattern.levelParams result.us) result.args

/--
Tries to rewrite `e` using the given theorem.
-/
public def Theorem.rewrite (thm : Theorem) (e : Expr) (d : Discharger := dischargeNone) : SimpM Result := do
  if let some result ← thm.pattern.match? e then
    -- **Note**: Potential optimization: check whether pattern covers all variables.
    for arg in result.args do
      let .mvar mvarId := arg | pure ()
      unless (← mvarId.isAssigned) do
        let decl ← mvarId.getDecl
        if let some val ← d decl.type then
          mvarId.assign val
        else
          -- **Note**: Failed to discharge hypothesis.
          return .rfl
    let proof := mkValue thm.expr thm.pattern result
    let rhs   := thm.rhs.instantiateLevelParams thm.pattern.levelParams result.us
    let rhs   ← shareCommonInc rhs
    let expr  ← instantiateRevBetaS rhs result.args
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
