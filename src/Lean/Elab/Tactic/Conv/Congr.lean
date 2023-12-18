/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Congr
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

private def congrImplies (mvarId : MVarId) : MetaM (List MVarId) := do
  let [mvarId₁, mvarId₂, _, _] ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr) | throwError "'apply implies_congr' unexpected result"
  let mvarId₁ ← markAsConvGoal mvarId₁
  let mvarId₂ ← markAsConvGoal mvarId₂
  return [mvarId₁, mvarId₂]

private def isImplies (e : Expr) : MetaM Bool :=
  if e.isArrow then
    isProp e.bindingDomain! <&&> isProp e.bindingBody!
  else
    return false

def congr (mvarId : MVarId) (addImplicitArgs := false) (nameSubgoals := true) :
    MetaM (List (Option MVarId)) := mvarId.withContext do
  let origTag ← mvarId.getTag
  let (lhs, rhs) ← getLhsRhsCore mvarId
  let lhs := (← instantiateMVars lhs).cleanupAnnotations
  if (← isImplies lhs) then
    return (← congrImplies mvarId).map Option.some
  else if lhs.isApp then
    let funInfo ← getFunInfo lhs.getAppFn
    let args := lhs.getAppArgs
    let some congrThm ← mkCongrSimp? lhs.getAppFn (subsingletonInstImplicitRhs := false)
      | throwError "'congr' conv tactic failed to create congruence theorem"
    unless args.size == congrThm.argKinds.size do
      throwError "'congr' conv tactic failed, unexpected number of arguments in congruence theorem"
    let mut proof := congrThm.proof
    let mut mvarIdsNew := #[]
    let mut mvarIdsNewInsts := #[]
    for i in [:args.size] do
      let arg := args[i]!
      let argInfo := funInfo.paramInfo[i]!
      match congrThm.argKinds[i]! with
      | .fixed | .cast =>
        proof := mkApp proof arg;
        if addImplicitArgs || argInfo.isExplicit then
          mvarIdsNew := mvarIdsNew.push none
      | .eq    =>
        if addImplicitArgs || argInfo.isExplicit then
          let tag ← if nameSubgoals then
            pure (appendTag origTag (← whnf (← inferType proof)).bindingName!)
          else pure origTag
          let (rhs, mvarNew) ← mkConvGoalFor arg tag
          proof := mkApp3 proof arg rhs mvarNew
          mvarIdsNew := mvarIdsNew.push (some mvarNew.mvarId!)
        else
          proof := mkApp3 proof arg arg (← mkEqRefl arg)
      | .subsingletonInst =>
        proof := mkApp proof arg
        let rhs ← mkFreshExprMVar (← whnf (← inferType proof)).bindingDomain!
        proof := mkApp proof rhs
        mvarIdsNewInsts := mvarIdsNewInsts.push (some rhs.mvarId!)
      | .heq | .fixedNoParam => unreachable!
    let some (_, _, rhs') := (← whnf (← inferType proof)).eq? | throwError "'congr' conv tactic failed, equality expected"
    unless (← isDefEqGuarded rhs rhs') do
      throwError "invalid 'congr' conv tactic, failed to resolve{indentExpr rhs}\n=?={indentExpr rhs'}"
    mvarId.assign proof
    return mvarIdsNew.toList ++ mvarIdsNewInsts.toList
  else
    throwError "invalid 'congr' conv tactic, application or implication expected{indentExpr lhs}"

@[builtin_tactic Lean.Parser.Tactic.Conv.congr] def evalCongr : Tactic := fun _ => do
  replaceMainGoal <| List.filterMap id (← congr (← getMainGoal))

private def selectIdx (tacticName : String) (mvarIds : List (Option MVarId)) (i : Int) :
  TacticM Unit := do
  if i >= 0 then
    let i := i.toNat
    if h : i < mvarIds.length then
      for mvarId? in mvarIds, j in [:mvarIds.length] do
        match mvarId? with
        | none => pure ()
        | some mvarId =>
          if i != j then
            mvarId.refl
      match mvarIds[i] with
      | none => throwError "cannot select argument"
      | some mvarId => replaceMainGoal [mvarId]
      return ()
  throwError "invalid '{tacticName}' conv tactic, application has only {mvarIds.length} (nondependent) argument(s)"

@[builtin_tactic Lean.Parser.Tactic.Conv.skip] def evalSkip : Tactic := fun _ => pure ()

@[builtin_tactic Lean.Parser.Tactic.Conv.lhs] def evalLhs : Tactic := fun _ => do
  let mvarIds ← congr (← getMainGoal) (nameSubgoals := false)
  selectIdx "lhs" mvarIds ((mvarIds.length : Int) - 2)

@[builtin_tactic Lean.Parser.Tactic.Conv.rhs] def evalRhs : Tactic := fun _ => do
  let mvarIds ← congr (← getMainGoal) (nameSubgoals := false)
  selectIdx "rhs" mvarIds ((mvarIds.length : Int) - 1)

@[builtin_tactic Lean.Parser.Tactic.Conv.arg] def evalArg : Tactic := fun stx => do
  match stx with
  | `(conv| arg $[@%$tk?]? $i:num) =>
    let i := i.getNat
    if i == 0 then
      throwError "invalid 'arg' conv tactic, index must be greater than 0"
    let i := i - 1
    let mvarIds ← congr (← getMainGoal) (addImplicitArgs := tk?.isSome) (nameSubgoals := false)
    selectIdx "arg" mvarIds i
  | _ => throwUnsupportedSyntax

def extLetBodyCongr? (mvarId : MVarId) (lhs rhs : Expr) : MetaM (Option MVarId) := do
  match lhs with
  | .letE n t v b _ =>
    let u₁ ← getLevel t
    let f := mkLambda n .default t b
    unless (← isTypeCorrect f) do
      throwError "failed to abstract let-expression, result is not type correct"
    let (β, u₂, f') ← withLocalDeclD n t fun a => do
      let type ← inferType (mkApp f a)
      let β ← mkLambdaFVars #[a] type
      let u₂ ← getLevel type
      let rhsBody ← mkFreshExprMVar type
      let f' ← mkLambdaFVars #[a] rhsBody
      let rhs' := mkLet n t v f'.bindingBody!
      unless (← isDefEq rhs rhs') do
        throwError "failed to go inside let-declaration, type error"
      return (β, u₂, f')
    let (arg, mvarId') ← withLocalDeclD n t fun x => do
      let eqLhs := f.beta #[x]
      let eqRhs := f'.beta #[x]
      let mvarNew ← mkFreshExprSyntheticOpaqueMVar (← mkEq eqLhs eqRhs)
      let arg ← mkLambdaFVars #[x] mvarNew
      return (arg, mvarNew.mvarId!)
    let val := mkApp6 (mkConst ``let_body_congr [u₁, u₂]) t β f f' v arg
    mvarId.assign val
    return some (← markAsConvGoal mvarId')
  | _ => return none

private def extCore (mvarId : MVarId) (userName? : Option Name) : MetaM MVarId :=
  mvarId.withContext do
    let (lhs, rhs) ← getLhsRhsCore mvarId
    let lhs := (← instantiateMVars lhs).cleanupAnnotations
    if let .forallE n d b bi := lhs then
      let u ← getLevel d
      let p : Expr := .lam n d b bi
      let userName ← if let some userName := userName? then pure userName else mkFreshBinderNameForTactic n
      let (q, h, mvarNew) ← withLocalDecl userName bi d fun a => do
        let pa := b.instantiate1 a
        let (qa, mvarNew) ← mkConvGoalFor pa
        let q ← mkLambdaFVars #[a] qa
        let h ← mkLambdaFVars #[a] mvarNew
        let rhs' ← mkForallFVars #[a] qa
        unless (← isDefEqGuarded rhs rhs') do
          throwError "invalid 'ext' conv tactic, failed to resolve{indentExpr rhs}\n=?={indentExpr rhs'}"
        return (q, h, mvarNew)
      let proof := mkApp4 (mkConst ``forall_congr [u]) d p q h
      mvarId.assign proof
      return mvarNew.mvarId!
    else if let some mvarId ← extLetBodyCongr? mvarId lhs rhs then
      return mvarId
    else
      let lhsType ← whnfD (← inferType lhs)
      unless lhsType.isForall do
        throwError "invalid 'ext' conv tactic, function or arrow expected{indentD m!"{lhs} : {lhsType}"}"
      let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``funext) | throwError "'apply funext' unexpected result"
      let userNames := if let some userName := userName? then [userName] else []
      let (_, mvarId) ← mvarId.introN 1 userNames
      markAsConvGoal mvarId

private def ext (userName? : Option Name) : TacticM Unit := do
  replaceMainGoal [← extCore (← getMainGoal) userName?]

@[builtin_tactic Lean.Parser.Tactic.Conv.ext] def evalExt : Tactic := fun stx => do
  let ids := stx[1].getArgs
  if ids.isEmpty then
    ext none
  else
    for id in ids do
      withRef id <| ext id.getId

end Lean.Elab.Tactic.Conv
