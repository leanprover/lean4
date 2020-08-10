/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util

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

end Meta
end Lean
