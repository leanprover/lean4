/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Assumption
import Lean.Meta.MatchUtil

namespace Lean.Meta

def contradictionCore (mvarId : MVarId) (useDecide : Bool) : MetaM Bool := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `contradiction
    for localDecl in (← getLCtx) do
      -- (h : ¬ p) (h' : p)
      if let some p ← matchNot? localDecl.type then
        if let some pFVarId ← findLocalDeclWithType? p then
          assignExprMVar mvarId (← mkAbsurd (← getMVarType mvarId) (mkFVar pFVarId) localDecl.toExpr)
          return true
      -- (h : False)
      if (← matchFalse localDecl.type) then
        assignExprMVar mvarId (← mkFalseElim (← getMVarType mvarId) localDecl.toExpr)
        return true
      -- (h : x ≠ x)
      if let some (_, lhs, rhs) ← matchNe? localDecl.type then
        if (← isDefEq lhs rhs) then
          assignExprMVar mvarId (← mkAbsurd (← getMVarType mvarId) (← mkEqRefl lhs) localDecl.toExpr)
          return true
      -- (h : ctor₁ ... = ctor₂ ...)
      if let some (_, lhs, rhs) ← matchEq? localDecl.type then
        if let some lhsCtor ← matchConstructorApp? lhs then
        if let some rhsCtor ← matchConstructorApp? rhs then
        if lhsCtor.name != rhsCtor.name then
          assignExprMVar mvarId (← mkNoConfusion (← getMVarType mvarId) localDecl.toExpr)
          return true
      -- (h : p) s.t. `decide p` evaluates to `false`
      if useDecide && !localDecl.type.hasFVar && !localDecl.type.hasFVar then
        try
          let d ← mkDecide localDecl.type
          let r ← withDefault <| whnf d
          if r.isConstOf ``false then
            let hn := mkAppN (mkConst ``ofDecideEqFalse) <| d.getAppArgs.push (← mkEqRefl d)
            assignExprMVar mvarId (← mkAbsurd (← getMVarType mvarId) localDecl.toExpr hn)
            return true
        catch _ =>
          pure ()
    return false

def contradiction (mvarId : MVarId ) (useDecide : Bool := true) : MetaM Unit :=
  unless (← contradictionCore mvarId useDecide) do
    throwTacticEx `contradiction mvarId ""

end Lean.Meta
