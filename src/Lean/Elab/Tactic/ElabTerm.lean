/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Tactic.Constructor
public import Lean.Meta.Tactic.Assert
public import Lean.Meta.Tactic.Cleanup
public import Lean.Meta.Tactic.Rename
public import Lean.Elab.Tactic.Config

public section

namespace Lean.Elab.Tactic
open Meta

/-! # `elabTerm` for Tactics and basic tactics that use it. -/

/--
Runs a term elaborator inside a tactic, finalizing elaboration with `Term.synthesizeSyntheticMVars`.
- `mayPostpone` controls the postponement behavior of `Term.synthesizeSyntheticMVars`.

This function ensures that term elaboration fails when backtracking,
i.e., in `first| tac term | other`.
-/
def runTermElab (k : TermElabM α) (mayPostpone := false) : TacticM α :=
  -- We disable incrementality here so that nested tactics do not unexpectedly use and affect the
  -- incrementality state of a calling incrementality-enabled tactic.
  Term.withoutTacticIncrementality true do
    /- If error recovery is disabled, we disable `Term.withoutErrToSorry` -/
    if (← read).recover then
      go
    else
      Term.withoutErrToSorry go
where
  go := k <* Term.synthesizeSyntheticMVars (postpone := .ofBool mayPostpone)

/-- Elaborate `stx` in the current `MVarContext`. If given, the `expectedType` will be used to help
elaboration but not enforced (use `elabTermEnsuringType` to enforce an expected type). -/
def elabTerm (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr :=
  withRef stx do instantiateMVars <| ← runTermElab (mayPostpone := mayPostpone) do
    Term.elabTerm stx expectedType?

/-- Elaborate `stx` in the current `MVarContext`. If given, the `expectedType` will be used to help
elaboration and then a `TypeMismatchError` will be thrown if the elaborated type doesn't match.  -/
def elabTermEnsuringType (stx : Syntax) (expectedType? : Option Expr) (mayPostpone := false) : TacticM Expr := do
  let e ← elabTerm stx expectedType? mayPostpone
  -- We do use `Term.ensureExpectedType` because we don't want coercions being inserted here.
  match expectedType? with
  | none => return e
  | some expectedType =>
    let eType ← inferType e
    -- We allow synthetic opaque metavars to be assigned in the following step since the `isDefEq` is not really
    -- part of the elaboration, but part of the tactic. See issue #492
    unless (← withAssignableSyntheticOpaque <| isDefEq eType expectedType) do
      Term.throwTypeMismatchError none expectedType eType e
    return e

def logUnassignedAndAbort (mvarIds : Array MVarId) : TacticM Unit := do
   if (← Term.logUnassignedUsingErrorInfos mvarIds) then
     throwAbortTactic

def filterOldMVars (mvarIds : Array MVarId) (mvarCounterSaved : Nat) : MetaM (Array MVarId) := do
  let mctx ← getMCtx
  return mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved

/--
Try to close main goal using `x target tag`, where `target` is the type of the main goal and `tag` is its user name.

If `checkNewUnassigned` is true, then throws an error if the resulting value has metavariables that were created during the execution of `x`.
If it is false, then it is the responsibility of `x` to add such metavariables to the goal list.

During the execution of `x`:
* The local context is that of the main goal.
* The goal list has the main goal removed.
* It is allowable to modify the goal list, for example with `Lean.Elab.Tactic.pushGoals`.

On failure, the main goal remains at the front of the goal list.
-/
def closeMainGoalUsing (tacName : Name) (x : Expr → Name → TacticM Expr) (checkNewUnassigned := true) : TacticM Unit := do
  let mvarCounterSaved := (← getMCtx).mvarCounter
  let mvarId ← popMainGoal
  Tactic.tryCatch
    (mvarId.withContext do
      let val ← x (← mvarId.getType) (← mvarId.getTag)
      if checkNewUnassigned then
        let mvars ← filterOldMVars (← getMVars val) mvarCounterSaved
        logUnassignedAndAbort mvars
      unless (← mvarId.checkedAssign val) do
        throwTacticEx tacName mvarId m!"attempting to close the goal using{indentExpr val}\nthis is often due occurs-check failure")
    (fun ex => do
      pushGoal mvarId
      throw ex)

@[builtin_tactic «exact»] def evalExact : Tactic := fun stx => do
  match stx with
  | `(tactic| exact $e) => closeMainGoalUsing `exact fun type _ => elabTermEnsuringType e type
  | _ => throwUnsupportedSyntax

def sortMVarIdArrayByIndex [MonadMCtx m] [Monad m] (mvarIds : Array MVarId) : m (Array MVarId) := do
  let mctx ← getMCtx
  return mvarIds.qsort fun mvarId₁ mvarId₂ =>
    let decl₁ := mctx.getDecl mvarId₁
    let decl₂ := mctx.getDecl mvarId₂
    if decl₁.index != decl₂.index then
      decl₁.index < decl₂.index
    else
      Name.quickLt mvarId₁.name mvarId₂.name

def sortMVarIdsByIndex [MonadMCtx m] [Monad m] (mvarIds : Array MVarId) : m (Array MVarId) :=
  return (← sortMVarIdArrayByIndex mvarIds)

/--
Execute `k`, and collect any fresh metavariables created during the execution of `k`.
-/
def collectFreshMVars [Monad m] [MonadLiftT MetaM m] (k : m Expr) : m (Expr × Array MVarId) := do
  let mvarCounterSaved := (← liftMetaM getMCtx).mvarCounter
  let val ← k
  let newMVarIds ← getMVarsNoDelayed val
  /- Filter out all mvars that were created prior to `k`. -/
  let newMVarIds ← filterOldMVars newMVarIds mvarCounterSaved
  /-
  We sort the new metavariable ids by index to ensure the new goals are ordered using the order the metavariables have been created.
  See issue #1682.
  Potential problem: if elaboration of subterms is delayed the order the new metavariables are created may not match the order they
  appear in the `.lean` file. We should tell users to prefer tagged goals.
  -/
  let newMVarIds ← liftMetaM <| sortMVarIdsByIndex newMVarIds
  return (val, newMVarIds)

/--
Execute `k`, and collect new "holes" in the resulting expression.

* `parentTag` and `tagSuffix` are used to tag untagged goals with `Lean.Elab.Tactic.tagUntaggedGoals`.
* If `allowNaturalHoles` is true, then `_`'s are allowed and create new goals.
-/
def withCollectingNewGoalsFrom (k : TacticM Expr) (parentTag : Name) (tagSuffix : Name) (allowNaturalHoles := false) : TacticM (Expr × List MVarId) :=
  /-
  When `allowNaturalHoles = true`, unassigned holes should become new metavariables, including `_`s.
  Thus, we set `holesAsSyntheticOpaque` to true if it is not already set to `true`.
  See issue #1681. We have the tactic
  ```
  `refine' (fun x => _)
  ```
  If we create a natural metavariable `?m` for `_` with type `Nat`, then when we try to abstract `x`,
  a new metavariable `?n` with type `Nat -> Nat` is created, and we assign `?m := ?n x`,
  and the resulting term is `fun x => ?n x`. Then, `getMVarsNoDelayed` would return `?n` as a new goal
  which would be confusing since it has type `Nat -> Nat`.
  -/
  if allowNaturalHoles then
    withTheReader Term.Context (fun ctx => { ctx with holesAsSyntheticOpaque := ctx.holesAsSyntheticOpaque || allowNaturalHoles }) do
      /-
      We also enable the assignment of synthetic metavariables, otherwise we will fail to
      elaborate terms such as `f _ x` where `f : (α : Type) → α → α` and `x : A`.

      IMPORTANT: This is not a perfect solution. For example, `isDefEq` will be able assign metavariables associated with `by ...`.
      This should not be an immediate problem since this feature is only used to implement `refine'`. If it becomes
      an issue in practice, we should add a new kind of opaque metavariable for `refine'`, and mark the holes created using `_`
      with it, and have a flag that allows us to assign this kind of metavariable, but prevents us from assigning metavariables
      created by the `by ...` notation.
      -/
      withAssignableSyntheticOpaque go
  else
    go
where
  go := do
    let (val, newMVarIds) ← collectFreshMVars k
    /- ignore let-rec auxiliary variables, they are synthesized automatically later -/
    let newMVarIds ← newMVarIds.filterM fun mvarId => return !(← Term.isLetRecAuxMVar mvarId)
    /- If `allowNaturalHoles := false`, all natural mvarIds must be assigned.
    Passing this guard ensures that `newMVarIds` does not contain unassigned natural mvars. -/
    unless allowNaturalHoles do
      let naturalMVarIds ← newMVarIds.filterM fun mvarId => return (← mvarId.getKind).isNatural
      logUnassignedAndAbort naturalMVarIds
    let newMVarIds := newMVarIds.toList
    tagUntaggedGoals parentTag tagSuffix newMVarIds
    return (val, newMVarIds)

/-- Elaborates `stx` and collects the `MVarId`s of any holes that were created during elaboration.

With `allowNaturalHoles := false` (the default), any new natural holes (`_`) which cannot
be synthesized during elaboration cause `elabTermWithHoles` to fail. (Natural goals appearing in
`stx` which were created prior to elaboration are permitted.)

Unnamed `MVarId`s are renamed to share the tag `parentTag?` (or the main goal's tag if `parentTag?` is `none`).
If multiple unnamed goals are encountered, `tagSuffix` is appended to this tag along with a numerical index.

Note:
* Previously-created `MVarId`s which appear in `stx` are not returned.
* All parts of `elabTermWithHoles` operate at the current `MCtxDepth`, and therefore may assign
metavariables.
* When `allowNaturalHoles := true`, `stx` is elaborated under `withAssignableSyntheticOpaque`,
meaning that `.syntheticOpaque` metavariables might be assigned during elaboration. This is a
consequence of the implementation. -/
def elabTermWithHoles (stx : Syntax) (expectedType? : Option Expr) (tagSuffix : Name) (allowNaturalHoles := false) (parentTag? : Option Name := none) : TacticM (Expr × List MVarId) := do
  withCollectingNewGoalsFrom (elabTermEnsuringType stx expectedType?) (← parentTag?.getDM getMainTag) tagSuffix allowNaturalHoles

/-- If `allowNaturalHoles == true`, then we allow the resultant expression to contain unassigned "natural" metavariables.
   Recall that "natural" metavariables are created for explicit holes `_` and implicit arguments. They are meant to be
   filled by typing constraints.
   "Synthetic" metavariables are meant to be filled by tactics and are usually created using the synthetic hole notation `?<hole-name>`. -/
def refineCore (stx : Syntax) (tagSuffix : Name) (allowNaturalHoles : Bool) : TacticM Unit := do
  withMainContext do
    let (val, mvarIds') ← elabTermWithHoles stx (← getMainTarget) tagSuffix allowNaturalHoles
    let mvarId ← getMainGoal
    let val ← instantiateMVars val
    if val == mkMVar mvarId then
      /- `val == mkMVar mvarId` is `true` when we've refined the main goal. Refining the main goal
      (e.g. `refine ?a` when `?a` is the main goal) is an unlikely practice; further, it shouldn't
      be possible to create new mvarIds during elaboration when doing so. But in the rare event
      that somehow this happens, this is how we ought to handle it. -/
      replaceMainGoal (mvarId :: mvarIds')
    else
      /- Ensure that the main goal does not occur in `val`. -/
      if val.findMVar? (· == mvarId) matches some _ then
        throwError "`refine` tactic failed, value{indentExpr val}\ndepends on the main goal metavariable `{mkMVar mvarId}`"
      mvarId.assign val
      replaceMainGoal mvarIds'

@[builtin_tactic «refine»] def evalRefine : Tactic := fun stx =>
  match stx with
  | `(tactic| refine $e) => refineCore e `refine (allowNaturalHoles := false)
  | _                    => throwUnsupportedSyntax

@[builtin_tactic «refine'»] def evalRefine' : Tactic := fun stx =>
  match stx with
  | `(tactic| refine' $e) => refineCore e `refine' (allowNaturalHoles := true)
  | _                     => throwUnsupportedSyntax

@[builtin_tactic «specialize»] def evalSpecialize : Tactic := fun stx => withMainContext do
  match stx with
  | `(tactic| specialize $e:term) =>
    let (e, mvarIds') ← elabTermWithHoles e none `specialize (allowNaturalHoles := true)
    let h := e.getAppFn
    if h.isFVar then
      let localDecl ← h.fvarId!.getDecl
      let mvarId ← (← getMainGoal).assert localDecl.userName (← inferType e).headBeta e
      let (_, mvarId) ← mvarId.intro1P
      let mvarId ← mvarId.tryClear h.fvarId!
      replaceMainGoal (mvarIds' ++ [mvarId])
    else
      throwError "`specialize` requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"
  | _ => throwUnsupportedSyntax

/--
   Given a tactic
   ```
   apply f
   ```
   we want the `apply` tactic to create all metavariables. The following
   definition will return `@f` for `f`. That is, it will **not** create
   metavariables for implicit arguments.
   A similar method is also used in Lean 3.
   This method is useful when applying lemmas such as:
   ```
   theorem infLeRight {s t : Set α} : s ⊓ t ≤ t
   ```
   where `s ≤ t` here is defined as
   ```
   ∀ {x : α}, x ∈ s → x ∈ t
   ```
-/
def elabTermForApply (stx : Syntax) (mayPostpone := true) : TacticM Expr := do
  if stx.isIdent then
    match (← Term.resolveId? stx (withInfo := true)) with
    | some e => return e
    | _      => pure ()
  elabTerm stx none mayPostpone

def getFVarId (id : Syntax) : TacticM FVarId := withRef id <| withMainContext do
  -- use apply-like elaboration to suppress insertion of implicit arguments
  let e ← withoutRecover <| elabTermForApply id (mayPostpone := false)
  match e with
  | Expr.fvar fvarId => return fvarId
  | _                => throwError "Unexpected term `{e}`; expected single reference to variable"

def getFVarIds (ids : Array Syntax) : TacticM (Array FVarId) := do
  withMainContext do ids.mapM getFVarId

def evalApplyLikeTactic (tac : MVarId → Expr → MetaM (List MVarId)) (e : Syntax) : TacticM Unit := do
  withMainContext do
    let mut val ← instantiateMVars (← elabTermForApply e)
    if val.isMVar then
      /-
      If `val` is a metavariable, we force the elaboration of postponed terms.
      This is useful for producing a more useful error message in examples such as
      ```
      example (h : P) : P ∨ Q := by
        apply .inl
      ```
      Recall that `apply` elaborates terms without using the expected type,
      and the notation `.inl` requires the expected type to be available.
      -/
      Term.synthesizeSyntheticMVarsNoPostponing
      val ← instantiateMVars val
    let mvarIds' ← tac (← getMainGoal) val
    Term.synthesizeSyntheticMVarsNoPostponing
    replaceMainGoal mvarIds'

@[builtin_tactic Lean.Parser.Tactic.apply] def evalApply : Tactic := fun stx =>
  match stx with
  | `(tactic| apply $t) => evalApplyLikeTactic (fun g e => g.apply e (term? := some m!"`{e}`")) t
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.constructor] def evalConstructor : Tactic := fun _ =>
  withMainContext do
    let mvarIds' ← (← getMainGoal).constructor
    Term.synthesizeSyntheticMVarsNoPostponing
    replaceMainGoal mvarIds'

@[builtin_tactic Lean.Parser.Tactic.withReducible] def evalWithReducible : Tactic := fun stx =>
  withReducible <| evalTactic stx[1]

@[builtin_tactic Lean.Parser.Tactic.withReducibleAndInstances] def evalWithReducibleAndInstances : Tactic := fun stx =>
  withReducibleAndInstances <| evalTactic stx[1]

@[builtin_tactic Lean.Parser.Tactic.withUnfoldingAll] def evalWithUnfoldingAll : Tactic := fun stx =>
  withTransparency TransparencyMode.all <| evalTactic stx[1]

@[builtin_tactic Lean.Parser.Tactic.withUnfoldingNone] def evalWithUnfoldingNone : Tactic := fun stx =>
  withTransparency TransparencyMode.none <| evalTactic stx[1]

/--
  Elaborate `stx`. If it is a free variable, return it. Otherwise, assert it, and return the free variable.
  Note that, the main goal is updated when `Meta.assert` is used in the second case. -/
def elabAsFVar (stx : Syntax) (userName? : Option Name := none) : TacticM FVarId :=
  withMainContext do
    let e ← elabTerm stx none
    match e with
    | .fvar fvarId => pure fvarId
    | _ =>
      let type ← inferType e
      let intro (userName : Name) (preserveBinderNames : Bool) : TacticM FVarId := do
        let mvarId ← getMainGoal
        let (fvarId, mvarId) ← liftMetaM do
          let mvarId ← mvarId.assert userName type e
          Meta.intro1Core mvarId preserveBinderNames
        replaceMainGoal [mvarId]
        return fvarId
      match userName? with
      | none          => intro `h false
      | some userName => intro userName true

@[builtin_tactic Lean.Parser.Tactic.rename] def evalRename : Tactic := fun stx =>
  match stx with
  | `(tactic| rename $typeStx:term => $h:ident) => do
    withMainContext do
      /- Remark: we also use `withoutRecover` to make sure `elabTerm` does not succeed
         using `sorryAx`, and we get `"failed to find ..."` which will not be logged because
         it contains synthetic sorry's -/
      let fvarId ← withoutModifyingState <| withNewMCtxDepth <| withoutRecover do
        let type ← elabTerm typeStx none (mayPostpone := true)
        let fvarId? ← (← getLCtx).findDeclRevM? fun localDecl => do
          if !localDecl.isImplementationDetail && (← isDefEq type localDecl.type) then return localDecl.fvarId else return none
        match fvarId? with
        | none => throwError "Failed to find a hypothesis with type{indentExpr type}"
        | some fvarId => return fvarId
      replaceMainGoal [← (← getMainGoal).rename fvarId h.getId]
  | _ => throwUnsupportedSyntax

end Lean.Elab.Tactic
