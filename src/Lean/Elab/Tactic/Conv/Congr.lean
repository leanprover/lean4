/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.Tactic.Conv.Basic

namespace Lean.Elab.Tactic.Conv
open Meta

def congr (mvarId : MVarId) : MetaM (List MVarId) :=
  withMVarContext mvarId do
    let (lhs, rhs) ← getLhsRhsCore mvarId
    let lhs ← instantiateMVars lhs
    trace[Meta.debug] "{lhs} = {rhs}"
    unless lhs.isApp do
      throwError "invalid 'congr' conv tactic, application expected{indentExpr lhs}"
    lhs.withApp fun f args => do
      let infos := (← getFunInfoNArgs f args.size).paramInfo
      let mut r := { expr := f : Simp.Result }
      let mut newGoals := #[]
      let mut i := 0
      for arg in args do
        let addGoal ←
          if i < infos.size && !infos[i].hasFwdDeps then
            pure true
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

@[builtinTactic Lean.Parser.Tactic.Conv.congr] def evalCongr : Tactic := fun stx => do
   replaceMainGoal (← congr (← getMainGoal))

@[builtinTactic Lean.Parser.Tactic.Conv.lhs] def evalLhs : Tactic := fun stx => do
   let [mvarId₁, mvarId₂] ← congr (← getMainGoal) | throwError "invalid 'lhs' conv tactic, binary application expected"
   applyRefl mvarId₂
   replaceMainGoal [mvarId₁]

@[builtinTactic Lean.Parser.Tactic.Conv.rhs] def evalRhs : Tactic := fun stx => do
   let [mvarId₁, mvarId₂] ← congr (← getMainGoal) | throwError "invalid 'rhs' conv tactic, binary application expected"
   applyRefl mvarId₁
   replaceMainGoal [mvarId₂]

@[builtinTactic Lean.Parser.Tactic.Conv.arg] def evalArg : Tactic := fun stx => do
   match stx with
   | `(conv| arg $i) =>
      let i := i.isNatLit?.getD 0
      if i == 0 then
        throwError "invalid 'arg' conv tactic, index must be greater than 0"
      let i := i - 1
      let mvarIds ← congr (← getMainGoal)
      if h : i < mvarIds.length then
        for mvarId in mvarIds, j in [:mvarIds.length] do
          if i != j then
            applyRefl mvarId
        replaceMainGoal [mvarIds.get i h]
      else
        throwError "invalid 'arg' conv tactic, application has only {mvarIds.length} (nondependent) arguments"
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
