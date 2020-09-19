/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.FVarSubst
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Revert

namespace Lean
namespace Meta

/--
  Convert the given goal `Ctx |- target` into `Ctx |- type -> target`.
  It assumes `val` has type `type` -/
def assert (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) : MetaM MVarId := do
withMVarContext mvarId $ do
  checkNotAssigned mvarId `assert;
  tag    ← getMVarTag mvarId;
  target ← getMVarType mvarId;
  let newType := Lean.mkForall name BinderInfo.default type target;
  newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag;
  assignExprMVar mvarId (mkApp newMVar val);
  pure newMVar.mvarId!

/--
  Convert the given goal `Ctx |- target` into `Ctx |- let name : type := val; target`.
  It assumes `val` has type `type` -/
def define (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) : MetaM MVarId := do
withMVarContext mvarId $ do
  checkNotAssigned mvarId `define;
  tag    ← getMVarTag mvarId;
  target ← getMVarType mvarId;
  let newType := Lean.mkLet name type val target;
  newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag;
  assignExprMVar mvarId newMVar;
  pure newMVar.mvarId!

/--
  Convert the given goal `Ctx |- target` into `Ctx |- forall (name : type) -> name = val -> target`.
  It assumes `val` has type `type` -/
def assertExt (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) (hName : Name := `h) : MetaM MVarId := do
withMVarContext mvarId $ do
  checkNotAssigned mvarId `assert;
  tag    ← getMVarTag mvarId;
  target ← getMVarType mvarId;
  u ← getLevel type;
  let hType := mkApp3 (mkConst `Eq [u]) type (mkBVar 0) val;
  let newType := Lean.mkForall name BinderInfo.default type $ Lean.mkForall hName BinderInfo.default hType target;
  newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag;
  rflPrf ← mkEqRefl val;
  assignExprMVar mvarId (mkApp2 newMVar val rflPrf);
  pure newMVar.mvarId!

structure AssertAfterResult :=
(fvarId : FVarId)
(mvarId : MVarId)
(subst  : FVarSubst)

/--
  Convert the given goal `Ctx |- target` into a goal containing `(userName : type)` after the local declaration with if `fvarId`.
  It assumes `val` has type `type`, and that `type` is well-formed after `fvarId`.
  Note that `val` does not need to be well-formed after `fvarId`. That is, it may contain variables that are defined after `fvarId`. -/
def assertAfter (mvarId : MVarId) (fvarId : FVarId) (userName : Name) (type : Expr) (val : Expr) : MetaM AssertAfterResult := do
withMVarContext mvarId $ do
  checkNotAssigned mvarId `assertAfter;
  tag        ← getMVarTag mvarId;
  target     ← getMVarType mvarId;
  localDecl  ← getLocalDecl fvarId;
  lctx       ← getLCtx;
  localInsts ← getLocalInstances;
  let fvarIds := lctx.foldlFrom (fun (fvarIds : Array FVarId) decl => fvarIds.push decl.fvarId) #[] (localDecl.index+1);
  let xs   := fvarIds.map mkFVar;
  targetNew ← mkForallFVars xs target;
  let targetNew := Lean.mkForall userName BinderInfo.default type targetNew;
  let lctxNew := fvarIds.foldl (fun (lctxNew : LocalContext) fvarId => lctxNew.erase fvarId) lctx;
  let localInstsNew := localInsts.filter fun inst => fvarIds.contains inst.fvar.fvarId!;
  mvarNew ← mkFreshExprMVarAt lctxNew localInstsNew targetNew MetavarKind.syntheticOpaque tag;
  let args := (fvarIds.filter fun fvarId => !(lctx.get! fvarId).isLet).map mkFVar;
  let args := #[val] ++ args;
  assignExprMVar mvarId (mkAppN mvarNew args);
  (fvarIdNew, mvarIdNew) ← intro1P mvarNew.mvarId!;
  (fvarIdsNew, mvarIdNew) ← introNP mvarIdNew fvarIds.size;
  let subst := fvarIds.size.fold
    (fun i (subst : FVarSubst) => subst.insert (fvarIds.get! i) (mkFVar (fvarIdsNew.get! i)))
    {};
  pure { fvarId := fvarIdNew, mvarId := mvarIdNew, subst := subst }

end Meta
end Lean
