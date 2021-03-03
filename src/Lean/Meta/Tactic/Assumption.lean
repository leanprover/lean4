/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.ExprDefEq
import Lean.Meta.Tactic.Util

namespace Lean.Meta

/-- Return a local declaration whose type is definitionally equal to `type`. -/
def findLocalDeclWithType? (type : Expr) : MetaM (Option FVarId) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isAuxDecl then
      return none
    else if (← isDefEq type localDecl.type) then
      return some localDecl.fvarId
    else
      return none

def assumptionCore (mvarId : MVarId) : MetaM Bool :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `assumption
    match (← findLocalDeclWithType? (← getMVarType mvarId)) with
    | none => return false
    | some fvarId => assignExprMVar mvarId (mkFVar fvarId); return true

def assumption (mvarId : MVarId) : MetaM Unit :=
  unless (← assumptionCore mvarId) do
    throwTacticEx `assumption mvarId ""

end Lean.Meta
