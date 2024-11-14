/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Constructor
import Lean.Meta.Tactic.Assert
import Lean.Meta.Tactic.AuxLemma
import Lean.Meta.Tactic.Cleanup
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Rename
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Config
import Lean.Elab.SyntheticMVars

namespace Lean.Elab.Tactic
open Meta

/-! # `elabTerm` for Tactics and basic tactics that use it. -/

/--
Runs a term elaborator inside a tactic.

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

def sortMVarIdsByIndex [MonadMCtx m] [Monad m] (mvarIds : List MVarId) : m (List MVarId) :=
  return (← sortMVarIdArrayByIndex mvarIds.toArray).toList

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
  elabTerm stx none mayPostpone

def getFVarId (id : Syntax) : TacticM FVarId := withRef id <| withMainContext do
  -- use apply-like elaboration to suppress insertion of implicit arguments
  let e ← withoutRecover <| elabTermForApply id (mayPostpone := false)
  match e with
  | Expr.fvar fvarId => return fvarId
  | _                => throwError "unexpected term '{e}'; expected single reference to variable"

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
  if expectedType.hasMVar then
    throwError "expected type must not contain meta variables{indentExpr expectedType}"
  if expectedType.hasFVar then
    throwError "expected type must not contain free variables{indentExpr expectedType}\n\
      Use the '+revert' option to automatically cleanup and revert free variables."
  return expectedType

/--
Given the decidable instance `inst`, reduces it and returns a decidable instance expression
in whnf that can be regarded as the reason for the failure of `inst` to fully reduce.
-/
private partial def blameDecideReductionFailure (inst : Expr) : MetaM Expr := withIncRecDepth do
  let inst ← whnf inst
  -- If it's the Decidable recursor, then blame the major premise.
  if inst.isAppOfArity ``Decidable.rec 5 then
    return ← blameDecideReductionFailure inst.appArg!
  -- If it is a matcher, look for a discriminant that's a Decidable instance to blame.
  if let .const c _ := inst.getAppFn then
    if let some info ← getMatcherInfo? c then
      if inst.getAppNumArgs == info.arity then
        let args := inst.getAppArgs
        for i in [0:info.numDiscrs] do
          let inst' := args[info.numParams + 1 + i]!
          if (← Meta.isClass? (← inferType inst')) == ``Decidable then
            let inst'' ← whnf inst'
            if !(inst''.isAppOf ``isTrue || inst''.isAppOf ``isFalse) then
              return ← blameDecideReductionFailure inst''
  return inst

private unsafe def elabNativeDecideCoreUnsafe (tacticName : Name) (expectedType : Expr) : TacticM Expr := do
  let d ← mkDecide expectedType
  let levels := (collectLevelParams {} expectedType).params.toList
  let auxDeclName ← Term.mkAuxName `_nativeDecide
  let decl := Declaration.defnDecl {
    name := auxDeclName
    levelParams := levels
    type := mkConst ``Bool
    value := d
    hints := .abbrev
    safety := .safe
  }
  addAndCompile decl
  -- get instance from `d`
  let s := d.appArg!
  let rflPrf ← mkEqRefl (toExpr true)
  let levelParams := levels.map .param
  let pf := mkApp3 (mkConst ``of_decide_eq_true) expectedType s <|
    mkApp3 (mkConst ``Lean.ofReduceBool) (mkConst auxDeclName levelParams) (toExpr true) rflPrf
  try
    let lemmaName ← mkAuxLemma levels expectedType pf
    return .const lemmaName levelParams
  catch ex =>
    -- Diagnose error
    throwError MessageData.ofLazyM (es := #[expectedType]) do
      let r ←
        try
          evalConst Bool auxDeclName
        catch ex =>
          return m!"\
            tactic '{tacticName}' failed, could not evaluate decidable instance. \
            Error: {ex.toMessageData}"
      if !r then
        return m!"\
          tactic '{tacticName}' evaluated that the proposition\
          {indentExpr expectedType}\n\
          is false"
      else
        return m!"tactic '{tacticName}' failed. Error: {ex.toMessageData}"

@[implemented_by elabNativeDecideCoreUnsafe]
private opaque elabNativeDecideCore (tacticName : Name) (expectedType : Expr) : TacticM Expr

def evalDecideCore (tacticName : Name) (cfg : Parser.Tactic.DecideConfig) : TacticM Unit := do
  if cfg.revert then
    -- In revert mode: clean up the local context and then revert everything that is left.
    liftMetaTactic1 fun g => do
      let g ← g.cleanup
      let (_, g) ← g.revert (clearAuxDeclsInsteadOfRevert := true) (← g.getDecl).lctx.getFVarIds
      return g
  closeMainGoalUsing tacticName fun expectedType _ => do
    if cfg.kernel && cfg.native then
      throwError "tactic '{tacticName}' failed, cannot simultaneously set both '+kernel' and '+native'"
    let expectedType ← preprocessPropToDecide expectedType
    if cfg.native then
      elabNativeDecideCore tacticName expectedType
    else if cfg.kernel then
      doKernel expectedType
    else
      doElab expectedType
where
  doElab (expectedType : Expr) : TacticM Expr := do
    let pf ← mkDecideProof expectedType
    -- Get instance from `pf`
    let s := pf.appFn!.appArg!
    let r ← withAtLeastTransparency .default <| whnf s
    if r.isAppOf ``isTrue then
      -- Success!
      -- While we have a proof from reduction, we do not embed it in the proof term,
      -- and instead we let the kernel recompute it during type checking from the following more
      -- efficient term. The kernel handles the unification `e =?= true` specially.
      return pf
    else
      diagnose expectedType s r
  doKernel (expectedType : Expr) : TacticM Expr := do
    let pf ← mkDecideProof expectedType
    -- Get instance from `pf`
    let s := pf.appFn!.appArg!
    -- Reduce the decidable instance to (hopefully!) `isTrue` by passing `pf` to the kernel.
    -- The `mkAuxLemma` function caches the result in two ways:
    -- 1. First, the function makes use of a `type`-indexed cache per module.
    -- 2. Second, once the proof is added to the environment, the kernel doesn't need to check the proof again.
    let levelsInType := (collectLevelParams {} expectedType).params
    -- Level variables occurring in `expectedType`, in ambient order
    let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
    try
      let lemmaName ← mkAuxLemma lemmaLevels expectedType pf
      return mkConst lemmaName (lemmaLevels.map .param)
    catch _ =>
      diagnose expectedType s none
  diagnose {α : Type} (expectedType s : Expr) (r? : Option Expr) : TacticM α :=
    -- Diagnose the failure, lazily so that there is no performance impact if `decide` isn't being used interactively.
    throwError MessageData.ofLazyM (es := #[expectedType]) do
      let r ← r?.getDM (withAtLeastTransparency .default <| whnf s)
      if r.isAppOf ``isTrue then
        return m!"\
          tactic '{tacticName}' failed. internal error: the elaborator is able to reduce the \
          '{.ofConstName ``Decidable}' instance, but the kernel is not able to"
      else if r.isAppOf ``isFalse then
        return m!"\
          tactic '{tacticName}' proved that the proposition\
          {indentExpr expectedType}\n\
          is false"
      -- Re-reduce the instance and collect diagnostics, to get all unfolded Decidable instances
      let (reason, unfoldedInsts) ← withoutModifyingState <| withOptions (fun opt => diagnostics.set opt true) do
        modifyDiag (fun _ => {})
        let reason ← withAtLeastTransparency .default <| blameDecideReductionFailure s
        let unfolded := (← get).diag.unfoldCounter.foldl (init := #[]) fun cs n _ => cs.push n
        let unfoldedInsts ← unfolded |>.qsort Name.lt |>.filterMapM fun n => do
          let e ← mkConstWithLevelParams n
          if (← Meta.isClass? (← inferType e)) == ``Decidable then
            return m!"'{.ofConst e}'"
          else
            return none
        return (reason, unfoldedInsts)
      let stuckMsg :=
        if unfoldedInsts.isEmpty then
          m!"Reduction got stuck at the '{.ofConstName ``Decidable}' instance{indentExpr reason}"
        else
          let instances := if unfoldedInsts.size == 1 then "instance" else "instances"
          m!"After unfolding the {instances} {.andList unfoldedInsts.toList}, \
          reduction got stuck at the '{.ofConstName ``Decidable}' instance{indentExpr reason}"
      let hint :=
        if reason.isAppOf ``Eq.rec then
          m!"\n\n\
          Hint: Reduction got stuck on '▸' ({.ofConstName ``Eq.rec}), \
          which suggests that one of the '{.ofConstName ``Decidable}' instances is defined using tactics such as 'rw' or 'simp'. \
          To avoid tactics, make use of functions such as \
          '{.ofConstName ``inferInstanceAs}' or '{.ofConstName ``decidable_of_decidable_of_iff}' \
          to alter a proposition."
        else if reason.isAppOf ``Classical.choice then
          m!"\n\n\
          Hint: Reduction got stuck on '{.ofConstName ``Classical.choice}', \
          which indicates that a '{.ofConstName ``Decidable}' instance \
          is defined using classical reasoning, proving an instance exists rather than giving a concrete construction. \
          The '{tacticName}' tactic works by evaluating a decision procedure via reduction, \
          and it cannot make progress with such instances. \
          This can occur due to the 'opened scoped Classical' command, which enables the instance \
          '{.ofConstName ``Classical.propDecidable}'."
        else
          MessageData.nil
      return m!"\
        tactic '{tacticName}' failed for proposition\
        {indentExpr expectedType}\n\
        since its '{.ofConstName ``Decidable}' instance\
        {indentExpr s}\n\
        did not reduce to '{.ofConstName ``isTrue}' or '{.ofConstName ``isFalse}'.\n\n\
        {stuckMsg}{hint}"

declare_config_elab elabDecideConfig Parser.Tactic.DecideConfig

@[builtin_tactic Lean.Parser.Tactic.decide] def evalDecide : Tactic := fun stx => do
  let cfg ← elabDecideConfig stx[1]
  evalDecideCore `decide cfg

@[builtin_tactic Lean.Parser.Tactic.decideBang] def evalDecideBang : Tactic := fun stx => do
  let cfg ← elabDecideConfig stx[1]
  let cfg := { cfg with kernel := true }
  evalDecideCore `decide! cfg

@[builtin_tactic Lean.Parser.Tactic.nativeDecide] def evalNativeDecide : Tactic := fun stx => do
  let cfg ← elabDecideConfig stx[1]
  let cfg := { cfg with native := true }
  evalDecideCore `native_decide cfg

end Lean.Elab.Tactic
