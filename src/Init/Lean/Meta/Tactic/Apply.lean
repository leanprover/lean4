/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Lean.Util.FindMVar
import Init.Lean.Meta.Message
import Init.Lean.Meta.ExprDefEq
import Init.Lean.Meta.SynthInstance
import Init.Lean.Meta.Tactic.Util

namespace Lean
namespace Meta

/-
  Compute the number of expected arguments and whether the result type is of the form
  (?m ...) where ?m is an unassigned metavariable.
-/
private def getExpectedNumArgsAux (e : Expr) : MetaM (Nat × Bool) :=
withReducible $ forallTelescopeReducing e $ fun xs body =>
  pure (xs.size, body.getAppFn.isMVar)

private def getExpectedNumArgs (e : Expr) : MetaM Nat := do
(numArgs, _) ← getExpectedNumArgsAux e;
pure numArgs

private def throwApplyError {α} (mvarId : MVarId) (eType : Expr) (targetType : Expr) : MetaM α :=
throwTacticEx `apply mvarId ("failed to unify" ++ indentExpr eType ++ Format.line ++ "with" ++ indentExpr targetType)

def synthAppInstances (tacticName : Name) (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) : MetaM Unit :=
newMVars.size.forM $ fun i =>
  when (binderInfos.get! i).isInstImplicit $ do
    let mvar := newMVars.get! i;
    mvarType ← inferType mvar;
    mvarVal  ← synthInstance mvarType;
    unlessM (isDefEq mvar mvarVal) $
      throwTacticEx tacticName mvarId ("failed to assign synthesized instance")

def appendParentTag (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) : MetaM Unit := do
parentTag ← getMVarTag mvarId;
unless parentTag.isAnonymous $
  newMVars.size.forM $ fun i =>
    let newMVarId := (newMVars.get! i).mvarId!;
    unlessM (isExprMVarAssigned newMVarId) $
    unless (binderInfos.get! i).isInstImplicit $ do
      currTag ← getMVarTag newMVarId;
      renameMVar newMVarId (parentTag ++ currTag.eraseMacroScopes)

private def dependsOnOthers (mvar : Expr) (otherMVars : Array Expr) : MetaM Bool :=
otherMVars.anyM $ fun otherMVar =>
  if mvar == otherMVar then pure false
  else do
    otherMVarType ← inferType otherMVar;
    pure $ (otherMVarType.findMVar? $ fun mvarId => mvarId == mvar.mvarId!).isSome

private def reorderNonDependentFirst (newMVars : Array Expr) : MetaM (List MVarId) := do
(nonDeps, deps) ← newMVars.foldlM
  (fun (acc : Array MVarId × Array MVarId) (mvar : Expr) => do
    let (nonDeps, deps) := acc;
    let currMVarId := mvar.mvarId!;
    condM (dependsOnOthers mvar newMVars)
      (pure (nonDeps, deps.push currMVarId))
      (pure (nonDeps.push currMVarId, deps)))
  (#[], #[]);
pure $ nonDeps.toList ++ deps.toList

inductive ApplyNewGoals
| nonDependentFirst | nonDependentOnly | all

def apply (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) :=
withMVarContext mvarId $ do
  checkNotAssigned mvarId `apply;
  targetType ← getMVarType mvarId;
  eType      ← inferType e;
  (numArgs, hasMVarHead) ← getExpectedNumArgsAux eType;
  numArgs    ← if !hasMVarHead then pure numArgs else do {
    targetTypeNumArgs ← getExpectedNumArgs targetType;
    pure (numArgs - targetTypeNumArgs)
  };
  (newMVars, binderInfos, eType) ← forallMetaTelescopeReducing eType (some numArgs);
  unlessM (isDefEq eType targetType) $ throwApplyError mvarId eType targetType;
  synthAppInstances `apply mvarId newMVars binderInfos;
  let val := mkAppN e newMVars;
  assignExprMVar mvarId val;
  appendParentTag mvarId newMVars binderInfos;
  newMVars ← newMVars.filterM $ fun mvar => not <$> isExprMVarAssigned mvar.mvarId!;
  -- TODO: add option `ApplyNewGoals` and implement other orders
  reorderNonDependentFirst newMVars

end Meta
end Lean
