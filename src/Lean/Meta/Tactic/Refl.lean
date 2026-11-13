/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Reduce
public import Lean.Meta.Tactic.Apply

public section

namespace Lean.Meta

/--
Close given goal using `Eq.refl`.

With (`check := false`), the elaborator does not check if the goal is actually a definitionaly
equality.

See `Lean.MVarId.applyRfl` for the variant that also consults `@[refl]` lemmas, and which
backs the `rfl` tactic.
-/
def _root_.Lean.MVarId.refl (mvarId : MVarId) (check := true) : MetaM Unit := do
  mvarId.withContext do
    mvarId.checkNotAssigned `refl
    let targetType ← mvarId.getType'
    unless targetType.isAppOfArity ``Eq 3 do
      throwTacticEx `rfl mvarId m!"equality expected{indentExpr targetType}"
    let lhs ← instantiateMVars targetType.appFn!.appArg!
    let rhs ← instantiateMVars targetType.appArg!
    if check then
      let success ← isDefEq lhs rhs
      unless success do
        throwTacticEx `rfl mvarId m!"equality lhs{indentExpr lhs}\nis not definitionally equal to rhs{indentExpr rhs}"
    let us := targetType.getAppFn.constLevels!
    let α := targetType.appFn!.appFn!.appArg!
    mvarId.assign (mkApp2 (mkConst ``Eq.refl  us) α lhs)

/--
Proves a goal with `rfl`, provided that no reduction step needs the constructor of a `String`
literal (see `Config.stringLitToCtor`). Otherwise, executes `prove`, and tries `rfl` without this
restriction if `prove` fails. `rfl` must throw an exception if it fails.
-/
def reflOrProve (rfl : MetaM Unit) (prove : MetaM Unit) : MetaM Unit := do
  try
    withoutStringLitToCtor rfl
  catch _ =>
    let s ← saveState
    try
      prove
    catch ex =>
      s.restore
      try rfl catch _ => throw ex

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
      | throwTacticEx `hrefl mvarId

end Lean.Meta
