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

/--
Convert the list of goals `mvarIds` into a masked list based on `funInfo` and `congrArgKinds`.
The output list length is equal to `congrArgKinds.size` If `addImplicitArgs = true`. Otherwise, the length is equal to the number of implicit arguments
The `i`-th element at the output is a some iff `congrArgKinds[i] == .eq`.
If `addImplicitArgs = true`, then goals corresponding to implicit arguments are closed using `assumption`.

This function assumes
- The number of `.eq`s in `congrArgKinds` is equal to `mvarId.length`.
- `funInfo.paramInfo.size = congrArgKinds.size`
-/
private def mkCongrThmMask? (funInfo : FunInfo) (congrArgKinds : Array CongrArgKind) (mvarIds : List MVarId) (addImplicitArgs : Bool): MetaM (List (Option MVarId)) := do
  let mut mvarIds := mvarIds
  let mut mvarIds? := #[]
  for i in [:congrArgKinds.size] do
    let kind := congrArgKinds[i]!
    let argInfo := funInfo.paramInfo[i]!
    if kind matches .eq then
      let mvarId :: mvarIds' := mvarIds | unreachable!
      mvarIds := mvarIds'
      if addImplicitArgs || argInfo.isExplicit then
        mvarIds? := mvarIds?.push (some (← markAsConvGoal mvarId))
      else
        mvarId.refl
    else if addImplicitArgs || argInfo.isExplicit then
      mvarIds? := mvarIds?.push none
  return mvarIds?.toList

def congr (mvarId : MVarId) (addImplicitArgs := false) : MetaM (List (Option MVarId)) :=
  mvarId.withContext do
    let tag ← mvarId.getTag
    let (lhs, _) ← getLhsRhsCore mvarId
    let lhs := lhs.cleanupAnnotations
    let mvarIds ← try mvarId.congr (closeEasy := false) catch _ => throwError "invalid 'congr' conv tactic, application or implication expected{indentExpr lhs}"
    mvarIds.forM fun mvarId => mvarId.setTag tag; mvarId.setKind .syntheticOpaque
    if lhs.isApp then
      let funInfo ← getFunInfo lhs.getAppFn
      let congrArgKinds := getCongrSimpKinds funInfo
      mkCongrThmMask? funInfo congrArgKinds mvarIds addImplicitArgs
    else
      mvarIds.mapM fun mvarId => return some (← markAsConvGoal mvarId)

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
            mvarId.refl
      match mvarIds[i] with
      | none => throwError "cannot select argument with forward dependencies"
      | some mvarId => replaceMainGoal [mvarId]
      return ()
  throwError "invalid '{tacticName}' conv tactic, application has only {mvarIds.length} (nondependent) argument(s)"

@[builtinTactic Lean.Parser.Tactic.Conv.skip] def evalSkip : Tactic := fun _ => pure ()

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
