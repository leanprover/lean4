/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

/-- Returns a list of new congruence subgoals, which contains `none` for each argument with
forward dependencies. -/
private def congrApp (mvarId : MVarId) (lhs rhs : Expr) (addImplicitArgs := false) :
   MetaM (List (Option MVarId)) :=
  -- TODO: add support for `[congr]` lemmas
  lhs.withApp fun f args => do
    let infos := (← getFunInfoNArgs f args.size).paramInfo
    let mut r := { expr := f : Simp.Result }
    let mut newGoals : Array (Option MVarId) := #[]
    let mut i := 0
    for arg in args do
      let addGoal ←
        if i < infos.size then
          pure (addImplicitArgs || infos[i]!.binderInfo.isExplicit)
        else
          pure (← whnfD (← inferType r.expr)).isArrow
      let hasFwdDep := i < infos.size && infos[i]!.hasFwdDeps
      if addGoal then
        if hasFwdDep then
          newGoals := newGoals.push none
          r ← Simp.mkCongrFun r arg
        else
          let (rhs, newGoal) ← mkConvGoalFor arg
          newGoals := newGoals.push newGoal.mvarId!
          r ← Simp.mkCongr r { expr := rhs, proof? := newGoal }
      else
        r ← Simp.mkCongrFun r arg
      i := i + 1
    let proof ← r.getProof
    unless (← isDefEqGuarded rhs r.expr) do
      throwError "invalid 'congr' conv tactic, failed to resolve{indentExpr rhs}\n=?={indentExpr r.expr}"
    mvarId.assign proof
    return newGoals.toList

private def congrImplies (mvarId : MVarId) : MetaM (List MVarId) := do
  let [mvarId₁, mvarId₂, _, _] ← mvarId.apply (← mkConstWithFreshMVarLevels ``implies_congr) | throwError "'apply implies_congr' unexpected result"
  let mvarId₁ ← markAsConvGoal mvarId₁
  let mvarId₂ ← markAsConvGoal mvarId₂
  return [mvarId₁, mvarId₂]

-- TODO: move?
def isImplies (e : Expr) : MetaM Bool :=
  if e.isArrow then
    isProp e.bindingDomain! <&&> isProp e.bindingBody!
  else
    return false

def congr (mvarId : MVarId) (addImplicitArgs := false) : MetaM (List (Option MVarId)) :=
  mvarId.withContext do
    let (lhs, rhs) ← getLhsRhsCore mvarId
    let lhs := (← instantiateMVars lhs).consumeMData
    if (← isImplies lhs) then
      return (← congrImplies mvarId).map Option.some
    else if lhs.isApp then
      congrApp mvarId lhs rhs addImplicitArgs
    else
      throwError "invalid 'congr' conv tactic, application or implication expected{indentExpr lhs}"

@[builtinTactic Lean.Parser.Tactic.Conv.congr] def evalCongr : Tactic := fun _ => do
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
            mvarId.applyRefl
      match mvarIds.get ⟨i, h⟩ with
      | none => throwError "cannot select argument with forward dependencies"
      | some mvarId => replaceMainGoal [mvarId]
      return ()
  throwError "invalid '{tacticName}' conv tactic, application has only {mvarIds.length} (nondependent) argument(s)"

@[builtinTactic Lean.Parser.Tactic.Conv.lhs] def evalLhs : Tactic := fun _ => do
   let mvarIds ← congr (← getMainGoal)
   selectIdx "lhs" mvarIds ((mvarIds.length : Int) - 2)

@[builtinTactic Lean.Parser.Tactic.Conv.rhs] def evalRhs : Tactic := fun _ => do
   let mvarIds ← congr (← getMainGoal)
   selectIdx "rhs" mvarIds ((mvarIds.length : Int) - 1)

@[builtinTactic Lean.Parser.Tactic.Conv.arg] def evalArg : Tactic := fun stx => do
   match stx with
   | `(conv| arg $[@%$tk?]? $i:num) =>
      let i := i.getNat
      if i == 0 then
        throwError "invalid 'arg' conv tactic, index must be greater than 0"
      let i := i - 1
      let mvarIds ← congr (← getMainGoal) (addImplicitArgs := tk?.isSome)
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
      trace[Meta.debug] "rhs: {rhs'}"
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
     let userNames := if let some userName := userName? then [userName] else []
     let (lhs, rhs) ← getLhsRhsCore mvarId
     let lhs ← instantiateMVars lhs
     if lhs.isForall then
       let [mvarId, _] ← mvarId.apply (← mkConstWithFreshMVarLevels ``forall_congr) | throwError "'apply forall_congr' unexpected result"
       let (_, mvarId) ← mvarId.introN 1 userNames
       markAsConvGoal mvarId
     else if let some mvarId ← extLetBodyCongr? mvarId lhs rhs then
       return mvarId
     else
       let lhsType ← whnfD (← inferType lhs)
       unless lhsType.isForall do
         throwError "invalid 'ext' conv tactic, function or arrow expected{indentD m!"{lhs} : {lhsType}"}"
       let [mvarId] ← mvarId.apply (← mkConstWithFreshMVarLevels ``funext) | throwError "'apply funext' unexpected result"
       let (_, mvarId) ← mvarId.introN 1 userNames
       markAsConvGoal mvarId

private def ext (userName? : Option Name) : TacticM Unit := do
  replaceMainGoal [← extCore (← getMainGoal) userName?]

@[builtinTactic Lean.Parser.Tactic.Conv.ext] def evalExt : Tactic := fun stx => do
  let ids := stx[1].getArgs
  if ids.isEmpty then
    ext none
  else
    for id in ids do
      withRef id <| ext id.getId

end Lean.Elab.Tactic.Conv
