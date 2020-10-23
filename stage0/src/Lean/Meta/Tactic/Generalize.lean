#lang lean4
/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.KAbstract
import Lean.Meta.Tactic.Util

namespace Lean.Meta

def generalize (mvarId : MVarId) (e : Expr) (x : Name) (failIfNotInTarget : Bool := true) : MetaM MVarId :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `generalize
    let tag ← getMVarTag mvarId
    let target ← getMVarType mvarId
    let target ← instantiateMVars target
    let targetAbst ← kabstract target e
    if failIfNotInTarget && !targetAbst.hasLooseBVars then
      throwTacticEx `generalize mvarId "failed to find expression in the target"
    let eType ← inferType e
    let targetNew := Lean.mkForall x BinderInfo.default eType targetAbst
    unless (← isTypeCorrect targetNew) do
      throwTacticEx `generalize mvarId "result is not type correct"
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    assignExprMVar mvarId (mkApp mvarNew e)
    pure mvarNew.mvarId!

end Lean.Meta
