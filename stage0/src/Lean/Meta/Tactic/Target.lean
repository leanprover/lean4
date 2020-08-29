/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Intro

namespace Lean
namespace Meta

/--
  Convert the given goal `Ctx |- target` into `Ctx |- targetNew` using an equality proof `eqProof : target = targetNew`.
  It assumes `eqProof` has type `target = targetNew` -/
def replaceTargetEq (mvarId : MVarId) (targetNew : Expr) (eqProof : Expr) : MetaM MVarId := do
withMVarContext mvarId $ do
  checkNotAssigned mvarId `replaceTarget;
  tag      ← getMVarTag mvarId;
  newMVar  ← mkFreshExprSyntheticOpaqueMVar targetNew tag;
  target   ← getMVarType mvarId;
  u        ← getLevel target;
  eq       ← mkEq target targetNew;
  newProof ← mkExpectedTypeHint eqProof eq;
  let newVal := mkAppN (Lean.mkConst `Eq.mpr [u]) #[target, targetNew, eqProof, newMVar];
  assignExprMVar mvarId newMVar;
  pure newMVar.mvarId!

/--
  Convert the given goal `Ctx | target` into `Ctx |- targetNew`. It assumes the goals are definitionally equal.
  We use the proof term
  ```
  @id target newMVar
  ```
  to create a checkpoint. -/
def replaceTargetDefEq (mvarId : MVarId) (targetNew : Expr) : MetaM MVarId :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `change;
  target  ← getMVarType mvarId;
  if target == targetNew then pure mvarId
  else do
    tag     ← getMVarTag mvarId;
    newMVar ← mkFreshExprSyntheticOpaqueMVar targetNew tag;
    newVal  ← mkExpectedTypeHint newMVar target;
    assignExprMVar mvarId newMVar;
    pure newMVar.mvarId!

def change (mvarId : MVarId) (targetNew : Expr) : MetaM MVarId :=
withMVarContext mvarId $ do
  target ← getMVarType mvarId;
  unlessM (isDefEq target targetNew) $
    throwTacticEx `change mvarId
      ("given type" ++ indentExpr targetNew ++ Format.line ++ "is not definitionally equal to" ++ indentExpr target);
  replaceTargetDefEq mvarId targetNew

def changeHypothesis (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) : MetaM MVarId := do
checkNotAssigned mvarId `changeHypothesis;
(xs, mvarId) ← revert mvarId #[fvarId] true;
withMVarContext mvarId do
  let numReverted := xs.size;
  target ← getMVarType mvarId;
  let checkDefEq (typeOld : Expr) : MetaM Unit := do {
    unlessM (isDefEq typeNew typeOld) $
      throwTacticEx `changeHypothesis mvarId
        ("given type" ++ indentExpr typeNew ++ Format.line ++ "is not definitionally equal to" ++ indentExpr typeOld)
  };
  let finalize (targetNew : Expr) : MetaM MVarId := do {
    mvarId ← replaceTargetDefEq mvarId targetNew;
    (_, mvarId) ← introN mvarId (numReverted-1) [] false;
    pure mvarId
  };
  match target with
  | Expr.forallE n d b c => do checkDefEq d; finalize (mkForall n c.binderInfo typeNew b)
  | Expr.letE n t v b _  => do checkDefEq t; finalize (mkLet n typeNew v b)
  | _ => throwTacticEx `changeHypothesis mvarId "unexpected auxiliary target"

end Meta
end Lean
