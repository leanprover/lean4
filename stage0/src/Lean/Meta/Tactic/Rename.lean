/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util

namespace Lean.Meta

def rename (mvarId : MVarId) (fvarId : FVarId) (newUserName : Name) : MetaM MVarId := withMVarContext mvarId do
  checkNotAssigned mvarId `rename
  let lctxNew := (← getLCtx).setUserName fvarId newUserName
  let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances) (← getMVarType mvarId) MetavarKind.syntheticOpaque (← getMVarTag mvarId)
  assignExprMVar mvarId mvarNew
  return mvarNew.mvarId!

end Lean.Meta
