/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AbstractNestedProofs
import Lean.Meta.Tactic.Util

namespace Lean.Meta.Grind

def _root_.Lean.MVarId.transformTarget (mvarId : MVarId) (f : Expr → MetaM Expr) : MetaM MVarId := mvarId.withContext do
  mvarId.checkNotAssigned `grind
  let tag ← mvarId.getTag
  let type ← mvarId.getType
  let typeNew ← f type
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar typeNew tag
  mvarId.assign mvarNew
  return mvarNew.mvarId!

/--
Unfold all `reducible` declarations occurring in `e`.
-/
def unfoldReducible (e : Expr) : MetaM Expr :=
  let pre (e : Expr) : MetaM TransformStep := do
    let .const declName _ := e.getAppFn | return .continue
    unless (← isReducible declName) do return .continue
    let some v ← unfoldDefinition? e | return .continue
    return .visit v
  Core.transform e (pre := pre)

/--
Unfold all `reducible` declarations occurring in the goal's target.
-/
def _root_.Lean.MVarId.unfoldReducible (mvarId : MVarId) : MetaM MVarId :=
  mvarId.transformTarget Grind.unfoldReducible

/--
Abstract nested proofs occurring in the goal's target.
-/
def _root_.Lean.MVarId.abstractNestedProofs (mvarId : MVarId) (mainDeclName : Name) : MetaM MVarId :=
  mvarId.transformTarget (Lean.Meta.abstractNestedProofs mainDeclName)

end Lean.Meta.Grind
