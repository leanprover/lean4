/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Clear

namespace Lean.Meta

def revert (mvarId : MVarId) (fvarIds : Array FVarId) (preserveOrder : Bool := false) : MetaM (Array FVarId × MVarId) := do
  if fvarIds.isEmpty then
    pure (#[], mvarId)
  else withMVarContext mvarId do
    checkNotAssigned mvarId `revert
    for fvarId in fvarIds do
      if (← getLocalDecl fvarId) |>.isAuxDecl then
        throwError "failed to revert {mkFVar fvarId}, it is an auxiliary declaration created to represent recursive definitions"
    let fvars := fvarIds.map mkFVar
    match MetavarContext.MkBinding.collectDeps (← getMCtx) (← getLCtx) fvars preserveOrder with
    | Except.error _     => throwError "failed to revert variables {fvars}"
    | Except.ok toRevert =>
      /- We should clear any `auxDecl` in `toRevert` -/
      let mut mvarId      := mvarId
      let mut toRevertNew := #[]
      for x in toRevert do
        if (← getLocalDecl x.fvarId!) |>.isAuxDecl then
          mvarId ← clear mvarId x.fvarId!
        else
          toRevertNew := toRevertNew.push x
      let tag ← getMVarTag mvarId
      -- TODO: the following code can be optimized because `MetavarContext.revert` will compute `collectDeps` again.
      -- We should factor out the relevat part

      -- Set metavariable kind to natural to make sure `revert` will assign it.
      setMVarKind mvarId MetavarKind.natural
      let (e, toRevert) ←
        try
          liftMkBindingM <| MetavarContext.revert toRevertNew mvarId preserveOrder
        finally
          setMVarKind mvarId MetavarKind.syntheticOpaque
      let mvar := e.getAppFn
      setMVarTag mvar.mvarId! tag
      return (toRevert.map Expr.fvarId!, mvar.mvarId!)

end Lean.Meta
