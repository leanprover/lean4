/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Util.ForEachExpr
import Lean.Elab.InfoTree.Main
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil
import Lean.Meta.Tactic.Util
import Lean.Meta.Tactic.Revert
import Lean.Meta.Tactic.Intro
import Lean.Meta.Tactic.Clear
import Lean.Meta.Tactic.Assert

namespace Lean.Meta

/--
  Convert the given goal `Ctx |- target` into `Ctx |- targetNew` using an equality proof `eqProof : target = targetNew`.
  It assumes `eqProof` has type `target = targetNew` -/
def _root_.Lean.MVarId.replaceTargetEq (mvarId : MVarId) (targetNew : Expr) (eqProof : Expr) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `replaceTarget
    let tag      ← mvarId.getTag
    let mvarNew  ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    let target   ← mvarId.getType
    let u        ← getLevel target
    let eq       ← mkEq target targetNew
    let newProof ← mkExpectedTypeHint eqProof eq
    let val  := mkAppN (Lean.mkConst `Eq.mpr [u]) #[target, targetNew, newProof, mvarNew]
    mvarId.assign val
    return mvarNew.mvarId!

/--
  Convert the given goal `Ctx |- target` into `Ctx |- targetNew`. It assumes the goals are definitionally equal.
  We use the proof term
  ```
  @id target mvarNew
  ```
  to create a checkpoint. -/
def _root_.Lean.MVarId.replaceTargetDefEq (mvarId : MVarId) (targetNew : Expr) : MetaM MVarId :=
  mvarId.withContext do
    mvarId.checkNotAssigned `change
    let target  ← mvarId.getType
    if target == targetNew then
      return mvarId
    else
      let tag     ← mvarId.getTag
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
      let newVal  ← mkExpectedTypeHint mvarNew target
      mvarId.assign newVal
      return mvarNew.mvarId!

private def replaceLocalDeclCore (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) (eqProof : Expr) : MetaM AssertAfterResult :=
  mvarId.withContext do
    let localDecl ← fvarId.getDecl
    let typeNewPr ← mkEqMP eqProof (mkFVar fvarId)
    /- `typeNew` may contain variables that occur after `fvarId`.
        Thus, we use the auxiliary function `findMaxFVar` to ensure `typeNew` is well-formed at the
        position we are inserting it.
        We must `instantiateMVars` first to ensure that there is no mvar in `typeNew` which is
        assigned to some later-occurring fvar. -/
    let (_, localDecl') ← findMaxFVar (← instantiateMVars typeNew) |>.run localDecl
    let result ← mvarId.assertAfter localDecl'.fvarId localDecl.userName typeNew typeNewPr
    (do let mvarIdNew ← result.mvarId.clear fvarId
        pure { result with mvarId := mvarIdNew })
    <|> pure result
where
  findMaxFVar (e : Expr) : StateRefT LocalDecl MetaM Unit :=
    e.forEach' fun e => do
      if e.isFVar then
        let localDecl' ← e.fvarId!.getDecl
        modify fun localDecl => if localDecl'.index > localDecl.index then localDecl' else localDecl
        return false
      else
        return e.hasFVar

/--
  Replace type of the local declaration with id `fvarId` with one with the same user-facing name, but with type `typeNew`.
  This method assumes `eqProof` is a proof that the type of `fvarId` is equal to `typeNew`.
  This tactic actually adds a new declaration and (tries to) clear the old one.
  If the old one cannot be cleared, then at least its user-facing name becomes inaccessible.

  The new local declaration is inserted at the soonest point after `fvarId` at which it is
  well-formed. That is, if `typeNew` involves declarations which occur later than `fvarId` in the
  local context, the new local declaration will be inserted immediately after the latest-occurring
  one. Otherwise, it will be inserted immediately after `fvarId`.

  Note: `replaceLocalDecl` should not be used when unassigned pending mvars might be present in
  `typeNew`, as these may later be synthesized to fvars which occur after `fvarId` (by e.g.
  `Term.withSynthesize` or `Term.synthesizeSyntheticMVars`) .
  -/
abbrev _root_.Lean.MVarId.replaceLocalDecl (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) (eqProof : Expr) : MetaM AssertAfterResult :=
  replaceLocalDeclCore mvarId fvarId typeNew eqProof

/--
Replace the type of `fvarId` at `mvarId` with `typeNew`.
Remark: this method assumes that `typeNew` is definitionally equal to the current type of `fvarId`.
-/
def _root_.Lean.MVarId.replaceLocalDeclDefEq (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) : MetaM MVarId := do
  mvarId.withContext do
    if typeNew == (← fvarId.getType) then
      return mvarId
    else
      let mvarDecl ← mvarId.getDecl
      let lctxNew := (← getLCtx).modifyLocalDecl fvarId (·.setType typeNew)
      let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances) mvarDecl.type mvarDecl.kind mvarDecl.userName
      mvarId.assign mvarNew
      return mvarNew.mvarId!

/--
Replace the target type of `mvarId` with `typeNew`.
If `checkDefEq = false`, this method assumes that `typeNew` is definitionally equal to the current target type.
If `checkDefEq = true`, throw an error if `typeNew` is not definitionally equal to the current target type.
-/
def _root_.Lean.MVarId.change (mvarId : MVarId) (targetNew : Expr) (checkDefEq := true) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType
  if checkDefEq then
    unless (← isDefEq target targetNew) do
      throwTacticEx `change mvarId m!"given type{indentExpr targetNew}\nis not definitionally equal to{indentExpr target}"
  mvarId.replaceTargetDefEq targetNew

/--
Executes the revert/intro pattern, running the continuation `k` after temporarily reverting
the given local variables from the local context of the metavariable `mvarId`,
and then re-introducing the local variables specified by `k`.

- `mvarId` is the goal metavariable to operate on.
- `fvarIds` is an array of `fvarIds` to revert in the order specified.
  An error is thrown if they cannot be reverted in order.
- `clearAuxDeclsInsteadOfRevert` is configuration passed to `Lean.MVarId.revert`.
- `k` is the continuation run once the local variables have been reverted.
  It is provided `mvarId` after the requested variables have been reverted along with the array of reverted variables.
  This array always contains `fvarIds`, but it may contain additional variables that were reverted due to dependencies.
  The continuation returns a value, a new goal, and an _aliasing array_.

Once `k` has completed, one variable is introduced per entry in the aliasing array.
* If the entry is `none`, the variable is just introduced.
* If the entry is `some fv` (where `fv` is a variable from `fvarIds`),
  the variable is introduced and then recorded as an alias of `fv` in the info tree.
  This for example causes the unused variable linter as seeing `fv` and this newly introduced variable as being "the same".

For example, if `k` leaves all the reverted variables in the same order,
having it return `fvars.map .some` as the aliasing array causes those variables to be re-introduced and aliased
to the original local variables.

Returns the value returned by `k` along with the resulting goal after variable introduction.

See `Lean.MVarId.changeLocalDecl` for an example. The motivation is that to work on a local variable,
you need to move it into the goal, alter the goal, and then bring it back into the local context,
all while keeping track of any other local variables that depend on this one.
-/
def _root_.Lean.MVarId.withReverted (mvarId : MVarId) (fvarIds : Array FVarId)
    (k : MVarId → Array FVarId → MetaM (α × Array (Option FVarId) × MVarId))
    (clearAuxDeclsInsteadOfRevert := false) : MetaM (α × MVarId) := do
  let (xs, mvarId) ← mvarId.revert fvarIds true clearAuxDeclsInsteadOfRevert
  let (r, xs', mvarId) ← k mvarId xs
  let (ys, mvarId) ← mvarId.introNP xs'.size
  mvarId.withContext do
    for x? in xs', y in ys do
      if let some x := x? then
        Elab.pushInfoLeaf (.ofFVarAliasInfo { id := y, baseId := x, userName := ← y.getUserName })
  return (r, mvarId)

/--
Replaces the type of the free variable `fvarId` with `typeNew`.

If `checkDefEq` is `true` then an error is thrown if `typeNew` is not definitionally
equal to the type of `fvarId`. Otherwise this function assumes `typeNew` and the type
of `fvarId` are definitionally equal.

This function is the same as `Lean.MVarId.changeLocalDecl` but makes sure to push substitution
information into the info tree.
-/
def _root_.Lean.MVarId.changeLocalDecl (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr)
    (checkDefEq := true) : MetaM MVarId := do
  mvarId.checkNotAssigned `changeLocalDecl
  let (_, mvarId) ← mvarId.withReverted #[fvarId] fun mvarId fvars => mvarId.withContext do
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless ← isDefEq typeNew typeOld do
          throwTacticEx `changeLocalDecl mvarId
            m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) := do
      return ((), fvars.map .some, ← mvarId.replaceTargetDefEq targetNew)
    match ← mvarId.getType with
    | .forallE n d b bi => do check d; finalize (.forallE n typeNew b bi)
    | .letE n t v b ndep => do check t; finalize (.letE n typeNew v b ndep)
    | _ => throwTacticEx `changeLocalDecl mvarId "unexpected auxiliary target"
  return mvarId

/--
Modify `mvarId` target type using `f`.
-/
def _root_.Lean.MVarId.modifyTarget (mvarId : MVarId) (f : Expr → MetaM Expr) : MetaM MVarId := do
  mvarId.withContext do
    mvarId.checkNotAssigned `modifyTarget
    mvarId.change (← f (← mvarId.getType)) (checkDefEq := false)

/--
Modify `mvarId` target type left-hand-side using `f`.
Throw an error if target type is not an equality.
-/
def _root_.Lean.MVarId.modifyTargetEqLHS (mvarId : MVarId) (f : Expr → MetaM Expr) : MetaM MVarId := do
   mvarId.modifyTarget fun target => do
     if let some (_, lhs, rhs) ← matchEq? target then
       mkEq (← f lhs) rhs
     else
       throwTacticEx `modifyTargetEqLHS mvarId m!"equality expected{indentExpr target}"

end Lean.Meta
