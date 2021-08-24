/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.FindMVar
import Lean.Meta.ExprDefEq
import Lean.Meta.SynthInstance
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.Util

namespace Lean.Meta

/-
  Compute the number of expected arguments and whether the result type is of the form
  (?m ...) where ?m is an unassigned metavariable.
-/
def getExpectedNumArgsAux (e : Expr) : MetaM (Nat × Bool) :=
  withDefault <| forallTelescopeReducing e fun xs body =>
    pure (xs.size, body.getAppFn.isMVar)

def getExpectedNumArgs (e : Expr) : MetaM Nat := do
  let (numArgs, _) ← getExpectedNumArgsAux e
  pure numArgs

private def throwApplyError {α} (mvarId : MVarId) (eType : Expr) (targetType : Expr) : MetaM α :=
  throwTacticEx `apply mvarId m!"failed to unify{indentExpr eType}\nwith{indentExpr targetType}"

def synthAppInstances (tacticName : Name) (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) : MetaM Unit :=
  newMVars.size.forM fun i => do
    if binderInfos[i].isInstImplicit then
      let mvar := newMVars[i]
      let mvarType ← inferType mvar
      let mvarVal  ← synthInstance mvarType
      unless (← isDefEq mvar mvarVal) do
        throwTacticEx tacticName mvarId "failed to assign synthesized instance"

def appendParentTag (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) : MetaM Unit := do
  let parentTag ← getMVarTag mvarId
  if newMVars.size == 1 then
    -- if there is only one subgoal, we inherit the parent tag
    setMVarTag newMVars[0].mvarId! parentTag
  else
    unless parentTag.isAnonymous do
      newMVars.size.forM fun i => do
        let newMVarId := newMVars[i].mvarId!
        unless (← isExprMVarAssigned newMVarId) do
          unless binderInfos[i].isInstImplicit do
            let currTag ← getMVarTag newMVarId
            setMVarTag newMVarId (appendTag parentTag currTag)

def postprocessAppMVars (tacticName : Name) (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) : MetaM Unit := do
  synthAppInstances tacticName mvarId newMVars binderInfos
  -- TODO: default and auto params
  appendParentTag mvarId newMVars binderInfos

private def dependsOnOthers (mvar : Expr) (otherMVars : Array Expr) : MetaM Bool :=
  otherMVars.anyM fun otherMVar => do
    if mvar == otherMVar then
      pure false
    else
      let otherMVarType ← inferType otherMVar
      return (otherMVarType.findMVar? fun mvarId => mvarId == mvar.mvarId!).isSome

private def reorderNonDependentFirst (newMVars : Array Expr) : MetaM (List MVarId) := do
  let (nonDeps, deps) ← newMVars.foldlM (init := (#[], #[])) fun (nonDeps, deps) mvar => do
    let currMVarId := mvar.mvarId!
    if (← dependsOnOthers mvar newMVars) then
      pure (nonDeps, deps.push currMVarId)
    else
      pure (nonDeps.push currMVarId, deps)
  return nonDeps.toList ++ deps.toList

inductive ApplyNewGoals where
  | nonDependentFirst | nonDependentOnly | all

def apply (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `apply
    let targetType ← getMVarType mvarId
    let eType      ← inferType e
    let mut (numArgs, hasMVarHead) ← getExpectedNumArgsAux eType
    unless hasMVarHead do
      let targetTypeNumArgs ← getExpectedNumArgs targetType
      numArgs := numArgs - targetTypeNumArgs
    let (newMVars, binderInfos, eType) ← forallMetaTelescopeReducing eType (some numArgs)
    unless (← isDefEq eType targetType) do throwApplyError mvarId eType targetType
    postprocessAppMVars `apply mvarId newMVars binderInfos
    let e ← instantiateMVars e
    assignExprMVar mvarId (mkAppN e newMVars)
    let newMVars ← newMVars.filterM fun mvar => not <$> isExprMVarAssigned mvar.mvarId!
    let otherMVarIds ← getMVarsNoDelayed e
    -- TODO: add option `ApplyNewGoals` and implement other orders
    let newMVarIds ← reorderNonDependentFirst newMVars
    let otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    result.forM headBetaMVarType
    return result

def splitAnd (mvarId : MVarId) : MetaM (List MVarId) := do
  saturate mvarId fun mvarId =>
    observing? <| apply mvarId (mkConst ``And.intro)

def applyRefl (mvarId : MVarId) (msg : MessageData := "refl failed") : MetaM Unit :=
  withMVarContext mvarId do
    let some [] ← observing? do apply mvarId (mkConst ``Eq.refl [← mkFreshLevelMVar])
      | throwTacticEx `refl mvarId msg

def exfalso (mvarId : MVarId) (msg : MessageData := "exfalso failed") : MetaM MVarId :=
  withMVarContext mvarId do
    let some [mvarId] ← observing? do apply mvarId (mkConst ``False.elim [← mkFreshLevelMVar])
      | throwTacticEx `exfalso mvarId msg
    return mvarId

end Lean.Meta
