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
/-- Controls which new mvars are turned in to goals by the `apply` tactic.
- `nonDependentFirst`  mvars that don't depend on other goals appear first in the goal list.
- `nonDependentOnly` only mvars that don't depend on other goals are added to goal list.
- `all` all unassigned mvars are added to the goal list.
-/
inductive ApplyNewGoals where
  | nonDependentFirst | nonDependentOnly | all

/-- Configures the behaviour of the `apply` tactic. -/
structure ApplyConfig where
  newGoals := ApplyNewGoals.nonDependentFirst
  /--
  If `synthAssignedInstances` is `true`, then `apply` will synthesize instance implicit arguments
  even if they have assigned by `isDefEq`, and then check whether the synthesized value matches the
  one inferred. The `congr` tactic sets this flag to false.
  -/
  synthAssignedInstances := true
  /--
  If `approx := true`, then we turn on `isDefEq` approximations. That is, we use
  the `approxDefEq` combinator.
  -/
  approx : Bool := true

/--
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

def synthAppInstances (tacticName : Name) (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) (synthAssignedInstances : Bool) : MetaM Unit :=
  newMVars.size.forM fun i => do
    if binderInfos[i]!.isInstImplicit then
      let mvar := newMVars[i]!
      if synthAssignedInstances || !(← mvar.mvarId!.isAssigned) then
        let mvarType ← inferType mvar
        let mvarVal  ← synthInstance mvarType
        unless (← isDefEq mvar mvarVal) do
          throwTacticEx tacticName mvarId "failed to assign synthesized instance"

def appendParentTag (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) : MetaM Unit := do
  let parentTag ← mvarId.getTag
  if newMVars.size == 1 then
    -- if there is only one subgoal, we inherit the parent tag
    newMVars[0]!.mvarId!.setTag parentTag
  else
    unless parentTag.isAnonymous do
      newMVars.size.forM fun i => do
        let mvarIdNew := newMVars[i]!.mvarId!
        unless (← mvarIdNew.isAssigned) do
          unless binderInfos[i]!.isInstImplicit do
            let currTag ← mvarIdNew.getTag
            mvarIdNew.setTag (appendTag parentTag currTag)

/--
If `synthAssignedInstances` is `true`, then `apply` will synthesize instance implicit arguments
even if they have assigned by `isDefEq`, and then check whether the synthesized value matches the
one inferred. The `congr` tactic sets this flag to false.
-/
def postprocessAppMVars (tacticName : Name) (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo) (synthAssignedInstances := true) : MetaM Unit := do
  synthAppInstances tacticName mvarId newMVars binderInfos synthAssignedInstances
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

private def reorderGoals (mvars : Array Expr) : ApplyNewGoals → MetaM (List MVarId)
  | ApplyNewGoals.nonDependentFirst => do
      let (nonDeps, deps) ← partitionDependentMVars mvars
      return nonDeps.toList ++ deps.toList
  | ApplyNewGoals.nonDependentOnly => do
      let (nonDeps, _) ← partitionDependentMVars mvars
      return nonDeps.toList
  | ApplyNewGoals.all => return mvars.toList.map Lean.Expr.mvarId!

/-- Custom `isDefEq` for the `apply` tactic -/
private def isDefEqApply (cfg : ApplyConfig) (a b : Expr) : MetaM Bool := do
  if cfg.approx then
    approxDefEq <| isDefEqGuarded a b
  else
    isDefEqGuarded a b

/--
Close the given goal using `apply e`.
-/
def _root_.Lean.MVarId.apply (mvarId : MVarId) (e : Expr) (cfg : ApplyConfig := {}) : MetaM (List MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `apply
    let targetType ← mvarId.getType
    let eType      ← inferType e
    let (numArgs, hasMVarHead) ← getExpectedNumArgsAux eType
    /-
    The `apply` tactic adds `_`s to `e`, and some of these `_`s become new goals.
    When `hasMVarHead` is `false` we try different numbers, until we find a type compatible with `targetType`.
    We used to try only `numArgs-targetTypeNumArgs` when `hasMVarHead = false`, but this is not always correct.
    For example, consider the following example
    ```
    example {α β} [LE_trans β] (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
      apply le_trans
      assumption
      assumption
    ```
    In this example, `targetTypeNumArgs = 1` because `LE` for functions is defined as
    ```
    instance {α : Type u} {β : Type v} [LE β] : LE (α → β) where
      le f g := ∀ i, f i ≤ g i
    ```
    -/
    let rangeNumArgs ← if hasMVarHead then
      pure [numArgs : numArgs+1]
    else
      let targetTypeNumArgs ← getExpectedNumArgs targetType
      pure [numArgs - targetTypeNumArgs : numArgs+1]
    /-
    Auxiliary function for trying to add `n` underscores where `n ∈ [i: rangeNumArgs.stop)`
    See comment above
    -/
    let rec go (i : Nat) : MetaM (Array Expr × Array BinderInfo) := do
      if i < rangeNumArgs.stop then
        let s ← saveState
        let (newMVars, binderInfos, eType) ← forallMetaTelescopeReducing eType i
        if (← isDefEqApply cfg eType targetType) then
          return (newMVars, binderInfos)
        else
          s.restore
          go (i+1)
      else
        let (_, _, eType) ← forallMetaTelescopeReducing eType (some rangeNumArgs.start)
        throwApplyError mvarId eType targetType
    let (newMVars, binderInfos) ← go rangeNumArgs.start
    postprocessAppMVars `apply mvarId newMVars binderInfos cfg.synthAssignedInstances
    let e ← instantiateMVars e
    mvarId.assign (mkAppN e newMVars)
    let newMVars ← newMVars.filterM fun mvar => not <$> mvar.mvarId!.isAssigned
    let otherMVarIds ← getMVarsNoDelayed e
    let newMVarIds ← reorderGoals newMVars cfg.newGoals
    let otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    result.forM (·.headBetaType)
    return result
termination_by go i => rangeNumArgs.stop - i

@[deprecated MVarId.apply]
def apply (mvarId : MVarId) (e : Expr) (cfg : ApplyConfig := {}) : MetaM (List MVarId) :=
  mvarId.apply e cfg

partial def splitAndCore (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.withContext do
    mvarId.checkNotAssigned `splitAnd
    let type ← mvarId.getType'
    if !type.isAppOfArity ``And 2 then
      return [mvarId]
    else
      let tag ← mvarId.getTag
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
      mvarId.assign val
      return s.toList

/--
Apply `And.intro` as much as possible to goal `mvarId`.
-/
abbrev _root_.Lean.MVarId.splitAnd (mvarId : MVarId) : MetaM (List MVarId) :=
  splitAndCore mvarId

@[deprecated MVarId.splitAnd]
def splitAnd (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.splitAnd

def _root_.Lean.MVarId.exfalso (mvarId : MVarId) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `exfalso
    let target ← instantiateMVars (← mvarId.getType)
    let u ← getLevel target
    let mvarIdNew ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False) (tag := (← mvarId.getTag))
    mvarId.assign (mkApp2 (mkConst ``False.elim [u]) target mvarIdNew)
    return mvarIdNew.mvarId!

end Lean.Meta
