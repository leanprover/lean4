/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Reduce
import Lean.Meta.Tactic.Util

namespace Lean.Meta

private def useKernel (lhs rhs : Expr) : MetaM Bool := do
  if lhs.hasFVar || lhs.hasMVar || rhs.hasFVar || rhs.hasMVar then
    return false
  else
    return (← getTransparency) matches TransparencyMode.default | TransparencyMode.all

/--
Close given goal using `Eq.refl`.
-/
def _root_.Lean.MVarId.refl (mvarId : MVarId) : MetaM Unit := do
  mvarId.withContext do
    mvarId.checkNotAssigned `refl
    let targetType ← mvarId.getType'
    unless targetType.isAppOfArity ``Eq 3 do
      throwTacticEx `rfl mvarId m!"equality expected{indentExpr targetType}"
    let lhs ← instantiateMVars targetType.appFn!.appArg!
    let rhs ← instantiateMVars targetType.appArg!
    let success ← if (← useKernel lhs rhs) then
      pure (Kernel.isDefEq (← getEnv) {} lhs rhs)
    else
      isDefEq lhs rhs
    unless success do
      throwTacticEx `rfl mvarId m!"equality lhs{indentExpr lhs}\nis not definitionally equal to rhs{indentExpr rhs}"
    let us := targetType.getAppFn.constLevels!
    let α := targetType.appFn!.appFn!.appArg!
    mvarId.assign (mkApp2 (mkConst ``Eq.refl  us) α lhs)

@[deprecated MVarId.refl]
def refl (mvarId : MVarId) : MetaM Unit := do
  mvarId.refl

end Lean.Meta
