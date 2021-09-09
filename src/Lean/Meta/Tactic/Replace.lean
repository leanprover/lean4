/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.ForEachExpr
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
def replaceTargetEq (mvarId : MVarId) (targetNew : Expr) (eqProof : Expr) : MetaM MVarId :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `replaceTarget
    let tag      ← getMVarTag mvarId
    let mvarNew  ← mkFreshExprSyntheticOpaqueMVar targetNew tag
    let target   ← getMVarType mvarId
    let u        ← getLevel target
    let eq       ← mkEq target targetNew
    let newProof ← mkExpectedTypeHint eqProof eq
    let val  := mkAppN (Lean.mkConst `Eq.mpr [u]) #[target, targetNew, eqProof, mvarNew]
    assignExprMVar mvarId val
    return mvarNew.mvarId!

/--
  Convert the given goal `Ctx | target` into `Ctx |- targetNew`. It assumes the goals are definitionally equal.
  We use the proof term
  ```
  @id target mvarNew
  ```
  to create a checkpoint. -/
def replaceTargetDefEq (mvarId : MVarId) (targetNew : Expr) : MetaM MVarId :=
  withMVarContext mvarId do
    checkNotAssigned mvarId `change
    let target  ← getMVarType mvarId
    if target == targetNew then
      return mvarId
    else
      let tag     ← getMVarTag mvarId
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew tag
      let newVal  ← mkExpectedTypeHint mvarNew target
      assignExprMVar mvarId mvarNew
      return mvarNew.mvarId!

/--
  Replace type of the local declaration with id `fvarId` with one with the same user-facing name, but with type `typeNew`.
  This method assumes `eqProof` is a proof that type of `fvarId` is equal to `typeNew`.
  This tactic actually adds a new declaration and (try to) clear the old one.
  If the old one cannot be cleared, then at least its user-facing name becomes inaccessible.
  Remark: the new declaration is added immediately after `fvarId`.
  `typeNew` must be well-formed at `fvarId`, but `eqProof` may contain variables declared after `fvarId`. -/
def replaceLocalDecl (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) (eqProof : Expr) : MetaM AssertAfterResult :=
  withMVarContext mvarId do
    let localDecl ← getLocalDecl fvarId
    let typeNewPr ← mkEqMP eqProof (mkFVar fvarId)
    -- `typeNew` may contain variables that occur after `fvarId`.
    -- Thus, we use the auxiliary function `findMaxFVar` to ensure `typeNew` is well-formed at the position we are inserting it.
    let (_, localDecl') ← findMaxFVar typeNew |>.run localDecl
    let result ← assertAfter mvarId localDecl'.fvarId localDecl.userName typeNew typeNewPr
    (do let mvarIdNew ← clear result.mvarId fvarId
        pure { result with mvarId := mvarIdNew })
    <|> pure result
where
  findMaxFVar (e : Expr) : StateRefT LocalDecl MetaM Unit :=
    e.forEach' fun e => do
      if e.isFVar then
        let localDecl' ← getLocalDecl e.fvarId!
        modify fun localDecl => if localDecl'.index > localDecl.index then localDecl' else localDecl
        return false
      else
        return e.hasFVar

def replaceLocalDeclDefEq (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) : MetaM MVarId := do
  withMVarContext mvarId do
    let mvarDecl ← getMVarDecl mvarId
    if typeNew == mvarDecl.type then
      return mvarId
    else
      let lctxNew := (← getLCtx).modifyLocalDecl fvarId (·.setType typeNew)
      let mvarNew ← mkFreshExprMVarAt lctxNew (← getLocalInstances) mvarDecl.type mvarDecl.kind mvarDecl.userName
      assignExprMVar mvarId mvarNew
      return mvarNew.mvarId!

def change (mvarId : MVarId) (targetNew : Expr) (checkDefEq := true) : MetaM MVarId := withMVarContext mvarId do
  let target ← getMVarType mvarId
  if checkDefEq then
    unless (← isDefEq target targetNew) do
      throwTacticEx `change mvarId m!"given type{indentExpr targetNew}\nis not definitionally equal to{indentExpr target}"
  replaceTargetDefEq mvarId targetNew

def changeLocalDecl (mvarId : MVarId) (fvarId : FVarId) (typeNew : Expr) (checkDefEq := true) : MetaM MVarId := do
  checkNotAssigned mvarId `changeLocalDecl
  let (xs, mvarId) ← revert mvarId #[fvarId] true
  withMVarContext mvarId do
    let numReverted := xs.size
    let target ← getMVarType mvarId
    let check (typeOld : Expr) : MetaM Unit := do
      if checkDefEq then
        unless (← isDefEq typeNew typeOld) do
          throwTacticEx `changeHypothesis mvarId m!"given type{indentExpr typeNew}\nis not definitionally equal to{indentExpr typeOld}"
    let finalize (targetNew : Expr) : MetaM MVarId := do
      let mvarId ← replaceTargetDefEq mvarId targetNew
      let (_, mvarId) ← introNP mvarId numReverted
      pure mvarId
    match target with
    | Expr.forallE n d b c => do check d; finalize (mkForall n c.binderInfo typeNew b)
    | Expr.letE n t v b _  => do check t; finalize (mkLet n typeNew v b)
    | _ => throwTacticEx `changeHypothesis mvarId "unexpected auxiliary target"

def modifyTarget (mvarId : MVarId) (f : Expr → MetaM Expr) : MetaM MVarId := do
  withMVarContext mvarId do
    checkNotAssigned mvarId `modifyTarget
    change mvarId (← f (← getMVarType mvarId)) (checkDefEq := false)

def modifyTargetEqLHS (mvarId : MVarId) (f : Expr → MetaM Expr) : MetaM MVarId := do
   modifyTarget mvarId fun target => do
     if let some (_, lhs, rhs) ← matchEq? target then
       mkEq (← f lhs) rhs
     else
       throwTacticEx `modifyTargetEqLHS mvarId m!"equality expected{indentExpr target}"

end Lean.Meta
