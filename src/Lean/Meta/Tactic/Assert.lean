/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.FVarSubst
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Revert

namespace Lean.Meta

/--
  Convert the given goal `Ctx |- target` into `Ctx |- type -> target`.
  It assumes `val` has type `type` -/
def _root_.Lean.MVarId.assert (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `assert
    let tag    ← mvarId.getTag
    let target ← mvarId.getType
    let newType := Lean.mkForall name BinderInfo.default type target
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag
    mvarId.assign (mkApp newMVar val)
    return newMVar.mvarId!

@[deprecated MVarId.assert]
def assert (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) : MetaM MVarId :=
  mvarId.assert name type val

/--
  Convert the given goal `Ctx |- target` into `Ctx |- let name : type := val; target`.
  It assumes `val` has type `type` -/
def _root_.Lean.MVarId.define (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) : MetaM MVarId := do
  mvarId.withContext do
    mvarId.checkNotAssigned `define
    let tag    ← mvarId.getTag
    let target ← mvarId.getType
    let newType := Lean.mkLet name type val target
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag
    mvarId.assign newMVar
    return newMVar.mvarId!

@[deprecated MVarId.define]
def define (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) : MetaM MVarId := do
  mvarId.define name type val

/--
  Convert the given goal `Ctx |- target` into `Ctx |- (hName : type) -> hName = val -> target`.
  It assumes `val` has type `type` -/
def _root_.Lean.MVarId.assertExt (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) (hName : Name := `h) : MetaM MVarId := do
  mvarId.withContext do
    mvarId.checkNotAssigned `assert
    let tag    ← mvarId.getTag
    let target ← mvarId.getType
    let u ← getLevel type
    let hType := mkApp3 (mkConst `Eq [u]) type (mkBVar 0) val
    let newType := Lean.mkForall name BinderInfo.default type $ Lean.mkForall hName BinderInfo.default hType target
    let newMVar ← mkFreshExprSyntheticOpaqueMVar newType tag
    let rflPrf ← mkEqRefl val
    mvarId.assign (mkApp2 newMVar val rflPrf)
    return newMVar.mvarId!

@[deprecated MVarId.assertExt]
def assertExt (mvarId : MVarId) (name : Name) (type : Expr) (val : Expr) (hName : Name := `h) : MetaM MVarId := do
  mvarId.assertExt name type val hName

structure AssertAfterResult where
  fvarId : FVarId
  mvarId : MVarId
  subst  : FVarSubst

/--
  Convert the given goal `Ctx |- target` into a goal containing `(userName : type)` after the local declaration with if `fvarId`.
  It assumes `val` has type `type`, and that `type` is well-formed after `fvarId`.
  Note that `val` does not need to be well-formed after `fvarId`. That is, it may contain variables that are defined after `fvarId`. -/
def _root_.Lean.MVarId.assertAfter (mvarId : MVarId) (fvarId : FVarId) (userName : Name) (type : Expr) (val : Expr) : MetaM AssertAfterResult := do
  mvarId.withContext do
    mvarId.checkNotAssigned `assertAfter
    let tag        ← mvarId.getTag
    let target     ← mvarId.getType
    let localDecl  ← fvarId.getDecl
    let lctx       ← getLCtx
    let localInsts ← getLocalInstances
    let fvarIds := lctx.foldl (init := #[]) (start := localDecl.index+1) fun fvarIds decl => fvarIds.push decl.fvarId
    let xs   := fvarIds.map mkFVar
    let targetNew ← mkForallFVars xs target (usedLetOnly := false)
    let targetNew := Lean.mkForall userName BinderInfo.default type targetNew
    let lctxNew := fvarIds.foldl (init := lctx) fun lctxNew fvarId => lctxNew.erase fvarId
    let localInstsNew := localInsts.filter fun inst => !fvarIds.contains inst.fvar.fvarId!
    let mvarNew ← mkFreshExprMVarAt lctxNew localInstsNew targetNew MetavarKind.syntheticOpaque tag
    let args := (fvarIds.filter fun fvarId => !(lctx.get! fvarId).isLet).map mkFVar
    let args := #[val] ++ args
    mvarId.assign (mkAppN mvarNew args)
    let (fvarIdNew, mvarIdNew) ← mvarNew.mvarId!.intro1P
    let (fvarIdsNew, mvarIdNew) ← mvarIdNew.introNP fvarIds.size
    let subst := fvarIds.size.fold (init := {}) fun i subst => subst.insert fvarIds[i]! (mkFVar fvarIdsNew[i]!)
    return { fvarId := fvarIdNew, mvarId := mvarIdNew, subst := subst }

@[deprecated MVarId.assertAfter]
def assertAfter (mvarId : MVarId) (fvarId : FVarId) (userName : Name) (type : Expr) (val : Expr) : MetaM AssertAfterResult := do
  mvarId.assertAfter fvarId userName type val

structure Hypothesis where
  userName : Name
  type     : Expr
  value    : Expr

/--
  Convert the given goal `Ctx |- target` into `Ctx, (hs[0].userName : hs[0].type) ... |-target`.
  It assumes `hs[i].val` has type `hs[i].type`. -/
def _root_.Lean.MVarId.assertHypotheses (mvarId : MVarId) (hs : Array Hypothesis) : MetaM (Array FVarId × MVarId) := do
  if hs.isEmpty then
    return (#[], mvarId)
  else mvarId.withContext do
    mvarId.checkNotAssigned `assertHypotheses
    let tag    ← mvarId.getTag
    let target ← mvarId.getType
    let targetNew := hs.foldr (init := target) fun h targetNew =>
      mkForall h.userName BinderInfo.default h.type targetNew
    let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    let val := hs.foldl (init := mvarNew) fun val h => mkApp val h.value
    mvarId.assign val
    mvarNew.mvarId!.introNP hs.size

@[deprecated MVarId.assertHypotheses]
def assertHypotheses (mvarId : MVarId) (hs : Array Hypothesis) : MetaM (Array FVarId × MVarId) := do
  mvarId.assertHypotheses hs

end Lean.Meta
