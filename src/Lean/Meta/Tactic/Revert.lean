/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Clear

namespace Lean.Meta

/--
Revert free variables `fvarIds` at goal `mvarId`.
-/
def _root_.Lean.MVarId.revert (mvarId : MVarId) (fvarIds : Array FVarId) (preserveOrder : Bool := false)
    (clearAuxDeclsInsteadOfRevert := false) : MetaM (Array FVarId × MVarId) := do
  if fvarIds.isEmpty then
    pure (#[], mvarId)
  else mvarId.withContext do
    mvarId.checkNotAssigned `revert
    unless clearAuxDeclsInsteadOfRevert do
      for fvarId in fvarIds do
        if (← fvarId.getDecl) |>.isAuxDecl then
          throwError "failed to revert {mkFVar fvarId}, it is an auxiliary declaration created to represent recursive definitions"
    let fvars := fvarIds.map mkFVar
    let toRevert ← collectForwardDeps fvars preserveOrder
    /- We should clear any `auxDecl` in `toRevert` -/
    let mut mvarId      := mvarId
    let mut toRevertNew := #[]
    for x in toRevert do
      if (← x.fvarId!.getDecl).isAuxDecl then
        mvarId ← mvarId.clear x.fvarId!
      else
        toRevertNew := toRevertNew.push x
    let tag ← mvarId.getTag
    -- TODO: the following code can be optimized because `MetavarContext.revert` will compute `collectDeps` again.
    -- We should factor out the relevant part

    -- Set metavariable kind to natural to make sure `revert` will assign it.
    mvarId.setKind .natural
    let (e, toRevert) ←
      try
        liftMkBindingM <| MetavarContext.revert toRevertNew mvarId preserveOrder
      finally
        mvarId.setKind .syntheticOpaque
    let mvar := e.getAppFn
    mvar.mvarId!.setTag tag
    return (toRevert.map Expr.fvarId!, mvar.mvarId!)

/-- Reverts all local declarations after `fvarId`. -/
def _root_.Lean.MVarId.revertAfter (mvarId : MVarId) (fvarId : FVarId) : MetaM (Array FVarId × MVarId) :=
  mvarId.withContext do
    let localDecl ← fvarId.getDecl
    let fvarIds := (← getLCtx).foldl (init := #[]) (start := localDecl.index+1) fun fvarIds decl => fvarIds.push decl.fvarId
    mvarId.revert fvarIds (preserveOrder := true) (clearAuxDeclsInsteadOfRevert := true)

@[deprecated MVarId.revert]
def revert (mvarId : MVarId) (fvarIds : Array FVarId) (preserveOrder : Bool := false) : MetaM (Array FVarId × MVarId) := do
  mvarId.revert fvarIds preserveOrder

end Lean.Meta
