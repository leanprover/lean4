/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util

namespace Lean.Meta

def clear (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `clear
    let lctx ← getLCtx
    unless lctx.contains fvarId do
      throwTacticEx `clear mvarId m!"unknown variable '{mkFVar fvarId}'"
    let tag ← getMVarTag mvarId
    let mctx ← getMCtx
    lctx.forM fun localDecl => do
      unless localDecl.fvarId == fvarId do
        if mctx.localDeclDependsOn localDecl fvarId then
          throwTacticEx `clear mvarId m!"variable '{localDecl.toExpr}' depends on '{mkFVar fvarId}'"
    let mvarDecl ← getMVarDecl mvarId
    if mctx.exprDependsOn mvarDecl.type fvarId then
      throwTacticEx `clear mvarId m!"target depends on '{mkFVar fvarId}'"
    let lctx := lctx.erase fvarId
    let localInsts ← getLocalInstances
    let localInsts := match localInsts.findIdx? $ fun localInst => localInst.fvar.fvarId! == fvarId with
      | none => localInsts
      | some idx => localInsts.eraseIdx idx
    let newMVar ← mkFreshExprMVarAt lctx localInsts mvarDecl.type MetavarKind.syntheticOpaque tag
    assignExprMVar mvarId newMVar
    pure newMVar.mvarId!

def tryClear (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId :=
  clear mvarId fvarId <|> pure mvarId

def tryClearMany (mvarId : MVarId) (fvarIds : Array FVarId) : MetaM MVarId := do
  fvarIds.foldrM (init := mvarId) fun fvarId mvarId => tryClear mvarId fvarId

end Lean.Meta
