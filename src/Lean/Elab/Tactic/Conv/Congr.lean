/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
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

private partial def mkCongrThm (origTag : Name) (f : Expr) (args : Array Expr) (addImplicitArgs := false) (nameSubgoals := true) :
    MetaM (Expr × Array (Option MVarId) × Array (Option MVarId)) := do
  let funInfo ← getFunInfoNArgs f args.size
  let some congrThm ← mkCongrSimpCore? f funInfo (← getCongrSimpKinds f funInfo) (subsingletonInstImplicitRhs := false)
    | throwError "'congr' conv tactic failed to create congruence theorem"
  let mut eNew := f
  let mut proof := congrThm.proof
  let mut mvarIdsNew := #[]
  let mut mvarIdsNewInsts := #[]
  for h : i in [:congrThm.argKinds.size] do
    let arg := args[i]!
    let argInfo := funInfo.paramInfo[i]!
    match congrThm.argKinds[i] with
    | .fixed | .cast =>
      eNew := mkApp eNew arg
      proof := mkApp proof arg;
      if addImplicitArgs || argInfo.isExplicit then
        mvarIdsNew := mvarIdsNew.push none
    | .eq =>
      if addImplicitArgs || argInfo.isExplicit then
        let tag ← if nameSubgoals then
          pure (appendTag origTag (← whnf (← inferType proof)).bindingName!)
        else pure origTag
        let (rhs, mvarNew) ← mkConvGoalFor arg tag
        eNew := mkApp eNew rhs
        proof := mkApp3 proof arg rhs mvarNew
        mvarIdsNew := mvarIdsNew.push (some mvarNew.mvarId!)
      else
        eNew := mkApp eNew arg
        proof := mkApp3 proof arg arg (← mkEqRefl arg)
    | .subsingletonInst =>
      proof := mkApp proof arg
      let rhs ← mkFreshExprMVar (← whnf (← inferType proof)).bindingDomain!
      eNew := mkApp eNew rhs
      proof := mkApp proof rhs
      mvarIdsNewInsts := mvarIdsNewInsts.push (some rhs.mvarId!)
    | .heq | .fixedNoParam => unreachable!
  if congrThm.argKinds.size < args.size then
    if congrThm.argKinds.size == 0 then
      throwError "'congr' conv tactic failed to create congruence theorem"
    let (proof', mvarIdsNew', mvarIdsNewInsts') ←
      mkCongrThm origTag eNew args[funInfo.getArity:] addImplicitArgs nameSubgoals
    for arg in args[funInfo.getArity:] do
      proof ← Meta.mkCongrFun proof arg
    proof ← mkEqTrans proof proof'
    mvarIdsNew := mvarIdsNew ++ mvarIdsNew'
    mvarIdsNewInsts := mvarIdsNewInsts ++ mvarIdsNewInsts'
  return (proof, mvarIdsNew, mvarIdsNewInsts)

def congr (mvarId : MVarId) (addImplicitArgs := false) (nameSubgoals := true) :
    MetaM (List (Option MVarId)) := mvarId.withContext do
  let origTag ← mvarId.getTag
  let (lhs, rhs) ← getLhsRhsCore mvarId
  let lhs := (← instantiateMVars lhs).cleanupAnnotations
  if (← isImplies lhs) then
    return (← congrImplies mvarId).map Option.some
  else if lhs.isApp then
    let (proof, mvarIdsNew, mvarIdsNewInsts) ←
      mkCongrThm origTag lhs.getAppFn lhs.getAppArgs addImplicitArgs nameSubgoals
    let some (_, _, rhs') := (← whnf (← inferType proof)).eq? | throwError "'congr' conv tactic failed, equality expected"
    unless (← isDefEqGuarded rhs rhs') do
      throwError "invalid 'congr' conv tactic, failed to resolve{indentExpr rhs}\n=?={indentExpr rhs'}"
    mvarId.assign proof
    return mvarIdsNew.toList ++ mvarIdsNewInsts.toList
  else
    throwError "invalid 'congr' conv tactic, application or implication expected{indentExpr lhs}"

@[builtin_tactic Lean.Parser.Tactic.Conv.congr] def evalCongr : Tactic := fun _ => do
  replaceMainGoal <| List.filterMap id (← congr (← getMainGoal))

-- mvarIds is the list of goals produced by congr. We only want to change the one at position `i`
-- so this closes all other equality goals with `rfl.`. There are non-equality goals produced
-- by `congr` (e.g. dependent instances), these are kept as goals.
private def selectIdx (tacticName : String) (mvarIds : List (Option MVarId)) (i : Int) :
  TacticM Unit := do
  if i >= 0 then
    let i := i.toNat
    if h : i < mvarIds.length then
      let mut otherGoals := #[]
      for mvarId? in mvarIds, j in [:mvarIds.length] do
        match mvarId? with
        | none => pure ()
        | some mvarId =>
          if i != j then
            if (← mvarId.getType').isEq then
              mvarId.refl
            else
              -- If its not an equality, it's likely a class constraint, to be left open
              otherGoals := otherGoals.push mvarId
      match mvarIds[i] with
      | none => throwError "cannot select argument"
      | some mvarId => replaceMainGoal (mvarId :: otherGoals.toList)
      return ()
  throwError "invalid '{tacticName}' conv tactic, application has only {mvarIds.length} (nondependent) argument(s)"

@[builtin_tactic Lean.Parser.Tactic.Conv.skip] def evalSkip : Tactic := fun _ => pure ()

@[builtin_tactic Lean.Parser.Tactic.Conv.lhs] def evalLhs : Tactic := fun _ => do
  let mvarIds ← congr (← getMainGoal) (nameSubgoals := false)
  selectIdx "lhs" mvarIds ((mvarIds.length : Int) - 2)

@[builtin_tactic Lean.Parser.Tactic.Conv.rhs] def evalRhs : Tactic := fun _ => do
  let mvarIds ← congr (← getMainGoal) (nameSubgoals := false)
  selectIdx "rhs" mvarIds ((mvarIds.length : Int) - 1)

/-- Implementation of `arg 0` -/
def congrFunN (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let (lhs, rhs) ← getLhsRhsCore mvarId
  let lhs := (← instantiateMVars lhs).cleanupAnnotations
  unless lhs.isApp do
    throwError "invalid 'arg 0' conv tactic, application expected{indentExpr lhs}"
  lhs.withApp fun f xs => do
    let (g, mvarNew) ← mkConvGoalFor f
    mvarId.assign (← xs.foldlM (fun mvar a => Meta.mkCongrFun mvar a) mvarNew)
    let rhs' := mkAppN g xs
    unless ← isDefEqGuarded rhs rhs' do
      throwError "invalid 'arg 0' conv tactic, failed to resolve{indentExpr rhs}\n=?={indentExpr rhs'}"
    return mvarNew.mvarId!

@[builtin_tactic Lean.Parser.Tactic.Conv.arg] def evalArg : Tactic := fun stx => do
  match stx with
  | `(conv| arg $[@%$tk?]? $i:num) =>
    let i := i.getNat
    if i == 0 then
      replaceMainGoal [← congrFunN (← getMainGoal)]
    else
      let i := i - 1
      let mvarIds ← congr (← getMainGoal) (addImplicitArgs := tk?.isSome) (nameSubgoals := false)
      selectIdx "arg" mvarIds i
  | _ => throwUnsupportedSyntax

@[builtin_tactic Lean.Parser.Tactic.Conv.«fun»] def evalFun : Tactic := fun _ => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let (lhs, rhs) ← getLhsRhsCore mvarId
    let lhs := (← instantiateMVars lhs).cleanupAnnotations
    let .app f a := lhs
      | throwError "invalid 'fun' conv tactic, application expected{indentExpr lhs}"
    let (g, mvarNew) ← mkConvGoalFor f
    mvarId.assign (← Meta.mkCongrFun mvarNew a)
    let rhs' := .app g a
    unless ← isDefEqGuarded rhs rhs' do
      throwError "invalid 'fun' conv tactic, failed to resolve{indentExpr rhs}\n=?={indentExpr rhs'}"
    replaceMainGoal [mvarNew.mvarId!]

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
