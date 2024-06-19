/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Siddhartha Gadgil
-/
prelude
import Lean.Util.FindMVar
import Lean.Meta.SynthInstance
import Lean.Meta.CollectMVars
import Lean.Meta.Tactic.Util
import Lean.PrettyPrinter

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
  If `allowSynthFailures` is `true`, then `apply` will return instance implicit arguments
  for which typeclass search failed as new goals.
  -/
  allowSynthFailures := false
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

private def throwApplyError {α} (mvarId : MVarId) (eType : Expr) (targetType : Expr) : MetaM α := do
  let explanation := MessageData.ofLazyM (es := #[eType, targetType]) do
    let (eType, targetType) ← addPPExplicitToExposeDiff eType targetType
    return m!"{indentExpr eType}\nwith{indentExpr targetType}"
  throwTacticEx `apply mvarId m!"failed to unify{explanation}"

def synthAppInstances (tacticName : Name) (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo)
    (synthAssignedInstances : Bool) (allowSynthFailures : Bool) : MetaM Unit :=
  newMVars.size.forM fun i => do
    if binderInfos[i]!.isInstImplicit then
      let mvar := newMVars[i]!
      if synthAssignedInstances || !(← mvar.mvarId!.isAssigned) then
        let mvarType ← inferType mvar
        try
          let mvarVal  ← synthInstance mvarType
          unless (← isDefEq mvar mvarVal) do
            throwTacticEx tacticName mvarId "failed to assign synthesized instance"
        catch e => unless allowSynthFailures do throw e

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
def postprocessAppMVars (tacticName : Name) (mvarId : MVarId) (newMVars : Array Expr) (binderInfos : Array BinderInfo)
    (synthAssignedInstances := true) (allowSynthFailures := false) : MetaM Unit := do
  synthAppInstances tacticName mvarId newMVars binderInfos synthAssignedInstances allowSynthFailures
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
      termination_by rangeNumArgs.stop - i
    let (newMVars, binderInfos) ← go rangeNumArgs.start
    postprocessAppMVars `apply mvarId newMVars binderInfos cfg.synthAssignedInstances cfg.allowSynthFailures
    let e ← instantiateMVars e
    mvarId.assign (mkAppN e newMVars)
    let newMVars ← newMVars.filterM fun mvar => not <$> mvar.mvarId!.isAssigned
    let otherMVarIds ← getMVarsNoDelayed e
    let newMVarIds ← reorderGoals newMVars cfg.newGoals
    let otherMVarIds := otherMVarIds.filter fun mvarId => !newMVarIds.contains mvarId
    let result := newMVarIds ++ otherMVarIds.toList
    result.forM (·.headBetaType)
    return result

@[deprecated MVarId.apply (since := "2022-07-15")]
def apply (mvarId : MVarId) (e : Expr) (cfg : ApplyConfig := {}) : MetaM (List MVarId) :=
  mvarId.apply e cfg

/-- Short-hand for applying a constant to the goal. -/
def _root_.Lean.MVarId.applyConst (mvar : MVarId) (c : Name) (cfg : ApplyConfig := {}) : MetaM (List MVarId) := do
  mvar.apply (← mkConstWithFreshMVarLevels c) cfg

end Meta

open Meta
namespace MVarId

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
abbrev splitAnd (mvarId : MVarId) : MetaM (List MVarId) :=
  splitAndCore mvarId

@[deprecated splitAnd] -- 2024-03-17
def _root_.Lean.Meta.splitAnd (mvarId : MVarId) : MetaM (List MVarId) :=
  mvarId.splitAnd

def exfalso (mvarId : MVarId) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `exfalso
    let target ← instantiateMVars (← mvarId.getType)
    let u ← getLevel target
    let mvarIdNew ← mkFreshExprSyntheticOpaqueMVar (mkConst ``False) (tag := (← mvarId.getTag))
    mvarId.assign (mkApp2 (mkConst ``False.elim [u]) target mvarIdNew)
    return mvarIdNew.mvarId!

/--
Apply the `n`-th constructor of the target type,
checking that it is an inductive type,
and that there are the expected number of constructors.
-/
def nthConstructor
    (name : Name) (idx : Nat) (expected? : Option Nat := none) (goal : MVarId) :
    MetaM (List MVarId) := do
  goal.withContext do
    goal.checkNotAssigned name
    matchConstInduct (← goal.getType').getAppFn
      (fun _ => throwTacticEx name goal "target is not an inductive datatype")
      fun ival us => do
        if let some e := expected? then unless ival.ctors.length == e do
          throwTacticEx name goal
            s!"{name} tactic works for inductive types with exactly {e} constructors"
        if h : idx < ival.ctors.length then
          goal.apply <| mkConst ival.ctors[idx] us
        else
          throwTacticEx name goal s!"index {idx} out of bounds, only {ival.ctors.length} constructors"

/--
Try to convert an `Iff` into an `Eq` by applying `iff_of_eq`.
If successful, returns the new goal, and otherwise returns the original `MVarId`.

This may be regarded as being a special case of `Lean.MVarId.liftReflToEq`, specifically for `Iff`.
-/
def iffOfEq (mvarId : MVarId) : MetaM MVarId := do
  let res ← observing? do
    let [mvarId] ← mvarId.apply (mkConst ``iff_of_eq []) | failure
    return mvarId
  return res.getD mvarId

/--
Try to convert an `Eq` into an `Iff` by applying `propext`.
If successful, then returns then new goal, otherwise returns the original `MVarId`.
-/
def propext (mvarId : MVarId) : MetaM MVarId := do
  let res ← observing? do
    -- Avoid applying `propext` if the target is not an equality of `Prop`s.
    -- We don't want a unification specializing `Sort*` to `Prop`.
    let tgt ← withReducible mvarId.getType'
    let some (_, x, _) := tgt.eq? | failure
    guard <| ← Meta.isProp x
    let [mvarId] ← mvarId.apply (mkConst ``propext []) | failure
    return mvarId
  return res.getD mvarId

/--
Try to close the goal using `proof_irrel_heq`. Returns whether or not it succeeds.

We need to be somewhat careful not to assign metavariables while doing this, otherwise we might
specialize `Sort _` to `Prop`.
-/
def proofIrrelHeq (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    let res ← observing? do
      mvarId.checkNotAssigned `proofIrrelHeq
      let tgt ← withReducible mvarId.getType'
      let some (_, lhs, _, rhs) := tgt.heq? | failure
      -- Note: `mkAppM` uses `withNewMCtxDepth`, which prevents `Sort _` from specializing to `Prop`
      let pf ← mkAppM ``proof_irrel_heq #[lhs, rhs]
      mvarId.assign pf
      return true
    return res.getD false

/--
Try to close the goal using `Subsingleton.elim`. Returns whether or not it succeeds.

We are careful to apply `Subsingleton.elim` in a way that does not assign any metavariables.
This is to prevent the `Subsingleton Prop` instance from being used as justification to specialize
`Sort _` to `Prop`.
-/
def subsingletonElim (mvarId : MVarId) : MetaM Bool :=
  mvarId.withContext do
    let res ← observing? do
      mvarId.checkNotAssigned `subsingletonElim
      let tgt ← withReducible mvarId.getType'
      let some (_, lhs, rhs) := tgt.eq? | failure
      -- Note: `mkAppM` uses `withNewMCtxDepth`, which prevents `Sort _` from specializing to `Prop`
      let pf ← mkAppM ``Subsingleton.elim #[lhs, rhs]
      mvarId.assign pf
      return true
    return res.getD false

end Lean.MVarId
