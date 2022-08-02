/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util

namespace Lean.Meta

/--
Erase the given free variable from the goal `mvarId`.
-/
def _root_.Lean.MVarId.clear (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `clear
    let lctx ← getLCtx
    unless lctx.contains fvarId do
      throwTacticEx `clear mvarId m!"unknown variable '{mkFVar fvarId}'"
    let tag ← mvarId.getTag
    lctx.forM fun localDecl => do
      unless localDecl.fvarId == fvarId do
        if (← localDeclDependsOn localDecl fvarId) then
          throwTacticEx `clear mvarId m!"variable '{localDecl.toExpr}' depends on '{mkFVar fvarId}'"
    let mvarDecl ← mvarId.getDecl
    if (← exprDependsOn mvarDecl.type fvarId) then
      throwTacticEx `clear mvarId m!"target depends on '{mkFVar fvarId}'"
    let lctx := lctx.erase fvarId
    let localInsts ← getLocalInstances
    let localInsts := match localInsts.findIdx? fun localInst => localInst.fvar.fvarId! == fvarId with
      | none => localInsts
      | some idx => localInsts.eraseIdx idx
    let newMVar ← mkFreshExprMVarAt lctx localInsts mvarDecl.type MetavarKind.syntheticOpaque tag
    mvarId.assign newMVar
    pure newMVar.mvarId!


@[deprecated MVarId.clear]
def clear (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId :=
  mvarId.clear fvarId

/--
Try to erase the given free variable from the goal `mvarId`. It is no-op if the free variable
cannot be erased due to forward dependencies.
-/
def _root_.Lean.MVarId.tryClear (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId :=
  mvarId.clear fvarId <|> pure mvarId

@[deprecated MVarId.tryClear]
def tryClear (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId :=
  mvarId.tryClear fvarId

/--
Try to erase the given free variables from the goal `mvarId`.
-/
def _root_.Lean.MVarId.tryClearMany (mvarId : MVarId) (fvarIds : Array FVarId) : MetaM MVarId := do
  fvarIds.foldrM (init := mvarId) fun fvarId mvarId => mvarId.tryClear fvarId

@[deprecated MVarId.tryClearMany]
def tryClearMany (mvarId : MVarId) (fvarIds : Array FVarId) : MetaM MVarId := do
  mvarId.tryClearMany fvarIds

end Lean.Meta
