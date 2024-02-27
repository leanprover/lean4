/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Constructor
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Rename
import Lean.Elab.Tactic.Basic
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Tactic
open Meta

/-! # `elabTerm` for Tactics and basic tactics that use it. -/

/--
Runs a term elaborator inside a tactic.

This function ensures that term elaboration fails when backtracking,
i.e., in `first| tac term | other`.
-/
def runTermElab (k : TermElabM α) (mayPostpone := false) : TacticM α := do
  /- If error recovery is disabled, we disable `Term.withoutErrToSorry` -/
  if (← read).recover then
    go
  else
    Term.withoutErrToSorry go
where
  go := k <* Term.synthesizeSyntheticMVars (mayPostpone := mayPostpone)

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

/-- Try to close main goal using `x target`, where `target` is the type of the main goal.  -/
def closeMainGoalUsing (x : Expr → TacticM Expr) (checkUnassigned := true) : TacticM Unit :=
  withMainContext do
    closeMainGoal (checkUnassigned := checkUnassigned) (← x (← getMainTarget))

def logUnassignedAndAbort (mvarIds : Array MVarId) : TacticM Unit := do
   if (← Term.logUnassignedUsingErrorInfos mvarIds) then
     throwAbortTactic

def filterOldMVars (mvarIds : Array MVarId) (mvarCounterSaved : Nat) : MetaM (Array MVarId) := do
  let mctx ← getMCtx
  return mvarIds.filter fun mvarId => (mctx.getDecl mvarId |>.index) >= mvarCounterSaved

@[builtin_tactic «exact»] def evalExact : Tactic := fun stx =>
  match stx with
  | `(tactic| exact $e) => closeMainGoalUsing (checkUnassigned := false) fun type => do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let r ← elabTermEnsuringType e type
    logUnassignedAndAbort (← filterOldMVars (← getMVars r) mvarCounterSaved)
    return r
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

def sortMVarIdsByIndex [MonadMCtx m] [Monad m] (mvarIds : List MVarId) : m (List MVarId) :=
  return (← sortMVarIdArrayByIndex mvarIds.toArray).toList

/--
  Execute `k`, and collect new "holes" in the resulting expression.
-/
def withCollectingNewGoalsFrom (k : TacticM Expr) (tagSuffix : Name) (allowNaturalHoles := false) : TacticM (Expr × List MVarId) :=
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
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let val ← k
    let newMVarIds ← getMVarsNoDelayed val
    /- ignore let-rec auxiliary variables, they are synthesized automatically later -/
    let newMVarIds ← newMVarIds.filterM fun mvarId => return !(← Term.isLetRecAuxMVar mvarId)
    /- Filter out all mvars that were created prior to `k`. -/
    let newMVarIds ← filterOldMVars newMVarIds mvarCounterSaved
    /- If `allowNaturalHoles := false`, all natural mvarIds must be assigned.
    Passing this guard ensures that `newMVarIds` does not contain unassigned natural mvars. -/
    unless allowNaturalHoles do
      let naturalMVarIds ← newMVarIds.filterM fun mvarId => return (← mvarId.getKind).isNatural
      logUnassignedAndAbort naturalMVarIds
    /-
    We sort the new metavariable ids by index to ensure the new goals are ordered using the order the metavariables have been created.
    See issue #1682.
    Potential problem: if elaboration of subterms is delayed the order the new metavariables are created may not match the order they
    appear in the `.lean` file. We should tell users to prefer tagged goals.
    -/
    let newMVarIds ← sortMVarIdsByIndex newMVarIds.toList
    tagUntaggedGoals (← getMainTag) tagSuffix newMVarIds
    return (val, newMVarIds)

/-- Elaborates `stx` and collects the `MVarId`s of any holes that were created during elaboration.

With `allowNaturalHoles := false` (the default), any new natural holes (`_`) which cannot
be synthesized during elaboration cause `elabTermWithHoles` to fail. (Natural goals appearing in
`stx` which were created prior to elaboration are permitted.)

Unnamed `MVarId`s are renamed to share the main goal's tag. If multiple unnamed goals are
encountered, `tagSuffix` is appended to the main goal's tag along with a numerical index.

Note:
* Previously-created `MVarId`s which appear in `stx` are not returned.
* All parts of `elabTermWithHoles` operate at the current `MCtxDepth`, and therefore may assign
metavariables.
* When `allowNaturalHoles := true`, `stx` is elaborated under `withAssignableSyntheticOpaque`,
meaning that `.syntheticOpaque` metavariables might be assigned during elaboration. This is a
consequence of the implementation. -/
def elabTermWithHoles (stx : Syntax) (expectedType? : Option Expr) (tagSuffix : Name) (allowNaturalHoles := false) : TacticM (Expr × List MVarId) := do
  withCollectingNewGoalsFrom (elabTermEnsuringType stx expectedType?) tagSuffix allowNaturalHoles

/-- If `allowNaturalHoles == true`, then we allow the resultant expression to contain unassigned "natural" metavariables.
   Recall that "natutal" metavariables are created for explicit holes `_` and implicit arguments. They are meant to be
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
        throwError "'refine' tactic failed, value{indentExpr val}\ndepends on the main goal metavariable '{mkMVar mvarId}'"
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
      throwError "'specialize' requires a term of the form `h x_1 .. x_n` where `h` appears in the local context"
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
  /-
    By disabling the "error recovery" (and consequently "error to sorry") feature,
    we make sure an `apply e` fails without logging an error message.
    The motivation is that `apply` is frequently used when writing tactic such as
    ```
    cases h <;> intro h' <;> first | apply t[h'] | ....
    ```
    Here the type of `h'` may be different in each case, and the term `t[h']` containing `h'` may even fail to
    be elaborated in some cases. When this happens we want the tactic to fail without reporting any error to the user,
    and the next tactic is tried.

    A drawback of disabling "error to sorry" is that there is no error recovery after the error is thrown, and features such
    as auto-completion are affected.

    By disabling "error to sorry", we also limit ourselves to at most one error at `t[h']`.

    By disabling "error to sorry", we also miss the opportunity to catch mistakes in tactic code such as
      `first | apply nonsensical-term | assumption`

    This should not be a big problem for the `apply` tactic since we usually provide small terms there.

    Note that we do not disable "error to sorry" at `exact` and `refine` since they are often used to elaborate big terms,
    and we do want error recovery there, and we want to see the error messages.

    We should probably provide options for allowing users to control this behavior.

    see issue #1037

    More complex solution:
      - We do not disable "error to sorry"
      - We elaborate term and check whether errors were produced
      - If there are other tactic branches and there are errors, we remove the errors from the log, and throw a new error to force the tactic to backtrack.
  -/
  withoutRecover <| elabTerm stx none mayPostpone

/--
Elaborate `id`, if the result is a free variable `x`, return `some x`, otherwise throw exception.
-/
def getFVarId (id : Syntax) : TacticM FVarId := withRef id do
  -- use apply-like elaboration to suppress insertion of implicit arguments
  let e ← withMainContext do elabTermForApply id (mayPostpone := false)
  let .fvar fvarId := e
    | throwError "unexpected term '{e}'; expected single reference to variable"
  return fvarId

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
  | `(tactic| apply $e) => evalApplyLikeTactic (·.apply) e
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
          if (← isDefEq type localDecl.type) then return localDecl.fvarId else return none
        match fvarId? with
        | none => throwError "failed to find a hypothesis with type{indentExpr type}"
        | some fvarId => return fvarId
      replaceMainGoal [← (← getMainGoal).rename fvarId h.getId]
  | _ => throwUnsupportedSyntax

/--
   Make sure `expectedType` does not contain free and metavariables.
   It applies zeta and zetaDelta-reduction to eliminate let-free-vars.
-/
private def preprocessPropToDecide (expectedType : Expr) : TermElabM Expr := do
  let mut expectedType ← instantiateMVars expectedType
  if expectedType.hasFVar then
    expectedType ← zetaReduce expectedType
  if expectedType.hasFVar || expectedType.hasMVar then
    throwError "expected type must not contain free or meta variables{indentExpr expectedType}"
  return expectedType

@[builtin_tactic Lean.Parser.Tactic.decide] def evalDecide : Tactic := fun _ =>
  closeMainGoalUsing fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let d ← mkDecide expectedType
    let d ← instantiateMVars d
    let r ← withDefault <| whnf d
    unless r.isConstOf ``true do
      throwError "failed to reduce to 'true'{indentExpr r}"
    let s := d.appArg! -- get instance from `d`
    let rflPrf ← mkEqRefl (toExpr true)
    return mkApp3 (Lean.mkConst ``of_decide_eq_true) expectedType s rflPrf

private def mkNativeAuxDecl (baseName : Name) (type value : Expr) : TermElabM Name := do
  let auxName ← Term.mkAuxName baseName
  let decl := Declaration.defnDecl {
    name := auxName, levelParams := [], type, value
    hints := .abbrev
    safety := .safe
  }
  addDecl decl
  compileDecl decl
  pure auxName

@[builtin_tactic Lean.Parser.Tactic.nativeDecide] def evalNativeDecide : Tactic := fun _ =>
  closeMainGoalUsing fun expectedType => do
    let expectedType ← preprocessPropToDecide expectedType
    let d ← mkDecide expectedType
    let auxDeclName ← mkNativeAuxDecl `_nativeDecide (Lean.mkConst `Bool) d
    let rflPrf ← mkEqRefl (toExpr true)
    let s := d.appArg! -- get instance from `d`
    return mkApp3 (Lean.mkConst ``of_decide_eq_true) expectedType s <| mkApp3 (Lean.mkConst ``Lean.ofReduceBool) (Lean.mkConst auxDeclName) (toExpr true) rflPrf

end Lean.Elab.Tactic
