/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.AppBuilder
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Assert

namespace Lean
namespace Meta

/--
  Convert the given goal `Ctx |- target` into `Ctx |- targetNew` using an equality proof `eqProof : target = targetNew`.
  It assumes `eqProof` has type `target = targetNew` -/
def replaceTargetEq (mvarId : MVarId) (targetNew : Expr) (eqProof : Expr) : MetaM MVarId :=
withMVarContext mvarId do
  checkNotAssigned mvarId `replaceTarget;
  tag      ← getMVarTag mvarId;
  mvarNew  ← mkFreshExprSyntheticOpaqueMVar targetNew tag;
  target   ← getMVarType mvarId;
  u        ← getLevel target;
  eq       ← mkEq target targetNew;
  newProof ← mkExpectedTypeHint eqProof eq;
  let newVal := mkAppN (Lean.mkConst `Eq.mpr [u]) #[target, targetNew, eqProof, mvarNew];
  assignExprMVar mvarId mvarNew;
  pure mvarNew.mvarId!

/--
  Convert the given goal `Ctx | target` into `Ctx |- targetNew`. It assumes the goals are definitionally equal.
  We use the proof term
  ```
  @id target mvarNew
  ```
  to create a checkpoint. -/
def replaceTargetDefEq (mvarId : MVarId) (targetNew : Expr) : MetaM MVarId :=
withMVarContext mvarId do
  checkNotAssigned mvarId `change;
  target  ← getMVarType mvarId;
  if target == targetNew then pure mvarId
  else do
    tag     ← getMVarTag mvarId;
    mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag;
    newVal  ← mkExpectedTypeHint mvarNew target;
    assignExprMVar mvarId mvarNew;
    pure mvarNew.mvarId!

/--
  Replace type of the local declaration with id `fvarId` with one with the same user-facing name, but with type `typeNew`.
  This method assumes `eqProof` is a proof that type of `fvarId` is equal to `typeNew`.
  This tactic actually adds a new declaration and (try to) clear the old one.
  If the old one cannot be cleared, then at least its user-facing name becomes inaccessible.
  Remark: the new declaration is added immediately after `fvarId`.
  `typeNew` must be well-formed at `fvarId`, but `eqProof` may contain variables declared after `fvarId`. -/
def replaceLocalDecl (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) (eqProof : Expr) : MetaM AssertAfterResult := do
withMVarContext mvarId $ do
  localDecl ← getLocalDecl fvarId;
  typeNewPr ← mkEqMP eqProof (mkFVar fvarId);
  result ← assertAfter mvarId localDecl.fvarId localDecl.userName typeNew typeNewPr;
  (do mvarIdNew ← clear result.mvarId fvarId; pure { result with mvarId := mvarIdNew }) <|> pure result

def change (mvarId : MVarId) (targetNew : Expr) : MetaM MVarId :=
withMVarContext mvarId do
  target ← getMVarType mvarId;
  unlessM (isDefEq target targetNew) $
    throwTacticEx `change mvarId
      ("given type" ++ indentExpr targetNew ++ Format.line ++ "is not definitionally equal to" ++ indentExpr target);
  replaceTargetDefEq mvarId targetNew

def changeLocalDecl (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) : MetaM MVarId := do
checkNotAssigned mvarId `changeLocalDecl;
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
