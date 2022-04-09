/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Reduce
import Lean.Meta.Tactic.Util

namespace Lean.Meta

def refl (mvarId : MVarId) : MetaM Unit := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `apply
    let targetType ← getMVarType' mvarId
    unless targetType.isAppOfArity ``Eq 3 do
      throwTacticEx `rfl mvarId "equality expected{indentExpr targetType}"
    let lhs ← instantiateMVars targetType.appFn!.appArg!
    let rhs ← instantiateMVars targetType.appArg!
    let success ←
      if (← useKernel lhs rhs) then
        pure (Kernel.isDefEq (← getEnv) {} lhs rhs)
      else
        isDefEq lhs rhs
    unless success do
      throwTacticEx `rfl mvarId m!"equality lhs{indentExpr lhs}\nis not definitionally equal to rhs{indentExpr rhs}"
    let us := targetType.getAppFn.constLevels!
    let α := targetType.appFn!.appFn!.appArg!
    assignExprMVar mvarId (mkApp2 (mkConst ``Eq.refl  us) α lhs)
where
  useKernel (lhs rhs : Expr) : MetaM Bool := do
    if lhs.hasFVar || lhs.hasMVar || rhs.hasFVar || rhs.hasMVar then
      return false
    else
      return (← getTransparency) matches TransparencyMode.default | TransparencyMode.all

end Lean.Meta
