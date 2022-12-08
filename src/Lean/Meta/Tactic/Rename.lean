/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util

namespace Lean.Meta

/--
Rename the user-face naming for the free variable `fvarId` at `mvarId`.
-/
def _root_.Lean.MVarId.rename (mvarId : MVarId) (fvarId : FVarId) (userNameNew : Name) : MetaM MVarId := mvarId.withContext do
  mvarId.checkNotAssigned `rename
  let lctxNew := (← getLCtx).setUserName fvarId userNameNew
  let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances) (← mvarId.getType) MetavarKind.syntheticOpaque (← mvarId.getTag)
  mvarId.assign mvarNew
  return mvarNew.mvarId!

@[deprecated MVarId.rename]
def rename (mvarId : MVarId) (fvarId : FVarId) (newUserName : Name) : MetaM MVarId :=
  mvarId.rename fvarId newUserName

end Lean.Meta
