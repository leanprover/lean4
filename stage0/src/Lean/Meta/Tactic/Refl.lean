/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Reduce
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Apply

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
      ofExceptKernelException (Kernel.isDefEq (← getEnv) {} lhs rhs)
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

@[deprecated MVarId.refl]
def _root_.Lean.MVarId.applyRefl (mvarId : MVarId) (msg : MessageData := "refl failed") : MetaM Unit :=
  try mvarId.refl catch _ => throwError msg

/--
Try to apply `heq_of_eq`. If successful, then return new goal, otherwise return `mvarId`.
-/
def _root_.Lean.MVarId.heqOfEq (mvarId : MVarId) : MetaM MVarId :=
  mvarId.withContext do
    let some [mvarId] ← observing? do mvarId.apply (mkConst ``heq_of_eq [← mkFreshLevelMVar]) | return mvarId
    return mvarId

/--
Try to apply `eq_of_heq`. If successful, then return new goal, otherwise return `mvarId`.
-/
def _root_.Lean.MVarId.eqOfHEq (mvarId : MVarId) : MetaM MVarId :=
  mvarId.withContext do
    let some [mvarId] ← observing? do mvarId.apply (mkConst ``eq_of_heq [← mkFreshLevelMVar]) | return mvarId
    return mvarId

/--
Close given goal using `HEq.refl`.
-/
def _root_.Lean.MVarId.hrefl (mvarId : MVarId) : MetaM Unit := do
  mvarId.withContext do
    let some [] ← observing? do mvarId.apply (mkConst ``HEq.refl [← mkFreshLevelMVar])
      | throwTacticEx `hrefl mvarId ""

end Lean.Meta
