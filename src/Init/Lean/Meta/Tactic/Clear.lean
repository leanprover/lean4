/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Meta.Tactic.Util

namespace Lean
namespace Meta

def clear (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `clear;
  lctx ← getLCtx;
  unless (lctx.contains fvarId) $
    throwTacticEx `clear mvarId ("unknown variable '" ++ mkFVar fvarId ++ "'");
  tag ← getMVarTag mvarId;
  mctx ← getMCtx;
  lctx.forM $ fun localDecl =>
    unless (localDecl.fvarId == fvarId) $
      when (mctx.localDeclDependsOn localDecl fvarId) $
        throwTacticEx `clear mvarId ("variable '" ++ localDecl.toExpr ++ "' depends on '" ++ mkFVar fvarId ++ "'");
  mvarDecl ← getMVarDecl mvarId;
  when (mctx.exprDependsOn mvarDecl.type fvarId) $
    throwTacticEx `clear mvarId ("taget depends on '" ++ mkFVar fvarId ++ "'");
  let lctx := lctx.erase fvarId;
  localInsts ← getLocalInstances;
  let localInsts := match localInsts.findIdx? $ fun localInst => localInst.fvar.fvarId! == fvarId with
    | none => localInsts
    | some idx => localInsts.eraseIdx idx;
  newMVar ← mkFreshExprMVarAt lctx localInsts mvarDecl.type tag MetavarKind.syntheticOpaque;
  modify $ fun s => { mctx := s.mctx.assignExpr mvarId newMVar, .. s };
  pure newMVar.mvarId!

end Meta
end Lean
