/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

private def congrApp (mvarId : MVarId) (lhs rhs : Expr) : MetaM (List MVarId) :=
  -- TODO: add support for `[congr]` lemmas
  lhs.withApp fun f args => do
    let infos := (← getFunInfoNArgs f args.size).paramInfo
    let mut r := { expr := f : Simp.Result }
    let mut newGoals := #[]
    let mut i := 0
    for arg in args do
      let addGoal ←
        if i < infos.size && !infos[i].hasFwdDeps then
          pure infos[i].binderInfo.isExplicit
        else
          pure (← whnfD (← inferType r.expr)).isArrow
      if addGoal then
        let (rhs, newGoal) ← mkConvGoalFor arg
        newGoals := newGoals.push newGoal.mvarId!
        r ← Simp.mkCongr r { expr := rhs, proof? := newGoal }
      else
        r ← Simp.mkCongrFun r arg
      i := i + 1
    let proof ← r.getProof
    unless (← isDefEqGuarded rhs r.expr) do
      throwError "invalid 'congr' conv tactic, failed to resolve{indentExpr rhs}\n=?={indentExpr r.expr}"
    assignExprMVar mvarId proof
    return newGoals.toList

private def congrImplies (mvarId : MVarId) : MetaM (List MVarId) := do
  let [mvarId₁, mvarId₂, _, _] ← apply mvarId (← mkConstWithFreshMVarLevels ``implies_congr) | throwError "'apply implies_congr' unexpected result"
  let mvarId₁ ← markAsConvGoal mvarId₁
  let mvarId₂ ← markAsConvGoal mvarId₂
  return [mvarId₁, mvarId₂]

-- TODO: move?
def isImplies (e : Expr) : MetaM Bool :=
  if e.isArrow then
    isProp e.bindingDomain! <&&> isProp e.bindingBody!
  else
    return false

def congr (mvarId : MVarId) : MetaM (List MVarId) :=
  withMVarContext mvarId do
    let (lhs, rhs) ← getLhsRhsCore mvarId
    let lhs ← instantiateMVars lhs
    trace[Meta.debug] "{lhs} = {rhs}"
    if (← isImplies lhs) then
      congrImplies mvarId
    else if lhs.isApp then
      congrApp mvarId lhs rhs
    else
      throwError "invalid 'congr' conv tactic, application or implication expected{indentExpr lhs}"

@[builtinTactic Lean.Parser.Tactic.Conv.congr] def evalCongr : Tactic := fun stx => do
   replaceMainGoal (← congr (← getMainGoal))

private def selectIdx (tacticName : String) (mvarIds : List MVarId) (i : Int) : TacticM Unit := do
  if i >= 0 then
    let i := i.toNat
    if h : i < mvarIds.length then
      for mvarId in mvarIds, j in [:mvarIds.length] do
        if i != j then
          applyRefl mvarId
      replaceMainGoal [mvarIds.get i h]
      return ()
  throwError "invalid '{tacticName}' conv tactic, application has only {mvarIds.length} (nondependent) argument(s)"

@[builtinTactic Lean.Parser.Tactic.Conv.lhs] def evalLhs : Tactic := fun stx => do
   let mvarIds ← congr (← getMainGoal)
   selectIdx "lhs" mvarIds ((mvarIds.length : Int) - 2)

@[builtinTactic Lean.Parser.Tactic.Conv.rhs] def evalRhs : Tactic := fun stx => do
   let mvarIds ← congr (← getMainGoal)
   selectIdx "rhs" mvarIds ((mvarIds.length : Int) - 1)

@[builtinTactic Lean.Parser.Tactic.Conv.arg] def evalArg : Tactic := fun stx => do
   match stx with
   | `(conv| arg $i) =>
      let i := i.isNatLit?.getD 0
      if i == 0 then
        throwError "invalid 'arg' conv tactic, index must be greater than 0"
      let i := i - 1
      let mvarIds ← congr (← getMainGoal)
      selectIdx "arg" mvarIds i
   | _ => throwUnsupportedSyntax

private def extCore (mvarId : MVarId) (userName? : Option Name) : MetaM MVarId :=
   withMVarContext mvarId do
     let userNames := if let some userName := userName? then [userName] else []
     let (lhs, rhs) ← getLhsRhsCore mvarId
     let lhs ← instantiateMVars lhs
     if lhs.isForall then
       let [mvarId, _] ← apply mvarId (← mkConstWithFreshMVarLevels ``forall_congr) | throwError "'apply forall_congr' unexpected result"
       let (_, mvarId) ← introN mvarId 1 userNames
       markAsConvGoal mvarId
     else
       let lhsType ← whnfD (← inferType lhs)
       unless lhsType.isForall do
         throwError "invalid 'ext' conv tactic, function or arrow expected{indentD m!"{lhs} : {lhsType}"}"
       let [mvarId] ← apply mvarId (← mkConstWithFreshMVarLevels ``funext) | throwError "'apply funext' unexpected result"
       let (_, mvarId) ← introN mvarId 1 userNames
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
