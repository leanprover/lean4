/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Util

namespace Lean.Meta.Grind

/--
Revert all free variables at goal `mvarId`.
-/
def _root_.Lean.MVarId.revertAll (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  mvarId.checkNotAssigned `revertAll
  let fvarIds := (← getLCtx).getFVarIds
  let fvars ← fvarIds.filterMapM fun fvarId => do
    if (← fvarId.getDecl).isAuxDecl then
      return none
    else
      return some (mkFVar fvarId)
  let tag ← mvarId.getTag
  mvarId.setKind .natural
  let (e, _) ←
    try
      liftMkBindingM <| MetavarContext.revert fvars mvarId (preserveOrder := true)
    finally
      mvarId.setKind .syntheticOpaque
  let mvar := e.getAppFn
  mvar.mvarId!.setTag tag
  return mvar.mvarId!

end Lean.Meta.Grind
