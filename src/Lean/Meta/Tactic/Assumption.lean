#lang lean4
/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.ExprDefEq
import Lean.Meta.Tactic.Util

namespace Lean.Meta

def assumptionAux (mvarId : MVarId) : MetaM Bool :=
withMVarContext mvarId do
  checkNotAssigned mvarId `assumption
  let mvarType ← getMVarType mvarId
  let lctx ← getLCtx
  let h? ← lctx.findDeclRevM? fun decl => do
    if decl.isAuxDecl then
      pure none
    else if (← isDefEq mvarType decl.type) then
      pure (some decl.toExpr)
    else
      pure none
  match h? with
  | some h => do assignExprMVar mvarId h; pure true
  | none   => pure false

def assumption (mvarId : MVarId) : MetaM Unit := do
unless (← assumptionAux mvarId) do
  throwTacticEx `assumption mvarId ""

end Lean.Meta
