/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util

namespace Lean.Meta

/-- Return a local declaration whose type is definitionally equal to `type`. -/
def findLocalDeclWithType? (type : Expr) : MetaM (Option FVarId) := do
  (← getLCtx).findDeclRevM? fun localDecl => do
    if localDecl.isImplementationDetail then
      return none
    else if (← isDefEq type localDecl.type) then
      return some localDecl.fvarId
    else
      return none

/-- Return `true` if managed to close goal `mvarId` using an assumption. -/
def _root_.Lean.MVarId.assumptionCore (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    mvarId.checkNotAssigned `assumption
    match (← findLocalDeclWithType? (← mvarId.getType)) with
    | none => return false
    | some fvarId => mvarId.assign (mkFVar fvarId); return true

@[deprecated MVarId.assumptionCore]
def assumptionCore (mvarId : MVarId) : MetaM Bool :=
  mvarId.assumptionCore

/-- Close goal `mvarId` using an assumption. Throw error message if failed. -/
def _root_.Lean.MVarId.assumption (mvarId : MVarId) : MetaM Unit :=
  unless (← mvarId.assumptionCore) do
    throwTacticEx `assumption mvarId ""

@[deprecated MVarId.assumption]
def assumption (mvarId : MVarId) : MetaM Unit :=
  mvarId.assumption

end Lean.Meta
