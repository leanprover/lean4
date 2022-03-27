/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.FindMVar
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
      return false
    else
      let otherMVarType ← inferType otherMVar
      return (otherMVarType.findMVar? fun mvarId => mvarId == mvar.mvarId!).isSome

/-- Partitions the given mvars in to two arrays (non-deps, deps)
according to whether the given mvar depends on other mvars in the array.-/
private def partitionDependentMVars (mvars : Array Expr) : MetaM (Array MVarId × Array MVarId) :=
  mvars.foldlM (init := (#[], #[])) fun (nonDeps, deps) mvar => do
    let currMVarId := mvar.mvarId!
    if (← dependsOnOthers mvar mvars) then
      return (nonDeps, deps.push currMVarId)
    else
      return (nonDeps.push currMVarId, deps)

/-- Controls which new mvars are turned in to goals by the `apply` tactic.
- `nonDependentFirst`  mvars that don't depend on other goals appear first in the goal list.
- `nonDependentOnly` only mvars that don't depend on other goals are added to goal list.
- `all` all unassigned mvars are added to the goal list.
-/
inductive ApplyNewGoals where
  | nonDependentFirst | nonDependentOnly | all

private def reorderGoals (mvars : Array Expr) : ApplyNewGoals → MetaM (List MVarId)
  | ApplyNewGoals.nonDependentFirst => do
      let (nonDeps, deps) ← partitionDependentMVars mvars
      return nonDeps.toList ++ deps.toList
  | ApplyNewGoals.nonDependentOnly => do
      let (nonDeps, deps) ← partitionDependentMVars mvars
      return nonDeps.toList
  | ApplyNewGoals.all => return mvars.toList.map Lean.Expr.mvarId!

/-- Configures the behaviour of the `apply` tactic. -/
structure ApplyConfig where
  newGoals := ApplyNewGoals.nonDependentFirst

def apply (mvarId : MVarId) (e : Expr) (cfg : ApplyConfig := {}) : MetaM (List MVarId) :=
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
    let newMVarIds ← reorderGoals newMVars cfg.newGoals
    let otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    result.forM headBetaMVarType
    return result

partial def splitAnd (mvarId : MVarId) : MetaM (List MVarId) :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `splitAnd
    let type ← getMVarType' mvarId
    if !type.isAppOfArity ``And 2 then
      return [mvarId]
    else
      let tag ← getMVarTag mvarId
      let rec go (type : Expr) : StateRefT (Array MVarId) MetaM Expr := do
        let type ← whnf type
        if type.isAppOfArity ``And 2 then
          let p₁ := type.appFn!.appArg!
          let p₂ := type.appArg!
          return mkApp4 (mkConst ``And.intro) p₁ p₂ (← go p₁) (← go p₂)
        else
          let idx := (← get).size + 1
          let mvar ← mkFreshExprSyntheticOpaqueMVar type (tag ++ (`h).appendIndexAfter idx)
          modify fun s => s.push mvar.mvarId!
          return mvar
      let (val, s) ← go type |>.run #[]
      assignExprMVar mvarId val
      return s.toList

def applyRefl (mvarId : MVarId) (msg : MessageData := "refl failed") : MetaM Unit :=
  withMVarContext mvarId do
    let some [] ← observing? do apply mvarId (mkConst ``Eq.refl [← mkFreshLevelMVar])
      | throwTacticEx `refl mvarId msg

def exfalso (mvarId : MVarId) (msg : MessageData := "exfalso failed") : MetaM MVarId :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `exfalso
    let target ← instantiateMVars (← getMVarType mvarId)
    let u ← getLevel target
    let mvarIdNew ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False) (tag := (← getMVarTag mvarId))
    assignExprMVar mvarId (mkApp2 (mkConst ``False.elim [u]) target mvarIdNew)
    return mvarIdNew.mvarId!

end Lean.Meta
