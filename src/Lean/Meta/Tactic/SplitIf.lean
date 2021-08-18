/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.LazyInitExtension
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Simp.Main

namespace Lean.Meta
namespace SplitIf

builtin_initialize ext : LazyInitExtension MetaM Simp.Context ←
  registerLazyInitExtension do
    let mut s : SimpLemmas := {}
    s ← s.addConst ``if_pos
    s ← s.addConst ``if_neg
    s ← s.addConst ``dif_pos
    s ← s.addConst ``dif_neg
    return {
      simpLemmas    := s
      congrLemmas   := (← getCongrLemmas)
      config.zeta   := false
      config.beta   := false
      config.eta    := false
      config.iota   := false
      config.proj   := false
      config.decide := false
    }

def getSimpContext : MetaM Simp.Context :=
  ext.get

def discharge? : Simp.Discharge := fun prop => do
  let prop ← instantiateMVars prop
  trace[Meta.splitIf] "discharge? {prop}, {prop.notNot?}"
  (← getLCtx).findDeclRevM? fun localDecl => do
     if localDecl.isAuxDecl then
       return none
     else if (← isDefEq prop localDecl.type) then
       return some localDecl.toExpr
     else match prop.notNot? with
       | none => return none
       | some arg =>
         if (← isDefEq arg localDecl.type) then
           return some (mkApp2 (mkConst ``not_not_intro) arg localDecl.toExpr)
         else
           return none

partial def findIfToSplit? (e : Expr) : Option Expr :=
  if let some iteApp := e.find? fun e => !e.hasLooseBVars && (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) then
    let cond := iteApp.getArg! 1 5
    findIfToSplit? cond |>.getD cond
  else
    none

def simpIfTarget (mvarId : MVarId) : MetaM MVarId := do
  trace[Meta.splitIf] "before simpIfTarget\n{MessageData.ofGoal mvarId}"
  if let some mvarId ← simpTarget mvarId (← getSimpContext) discharge? then
    trace[Meta.splitIf] "after simpIfTarget\n{MessageData.ofGoal mvarId}"
    return mvarId
  else
    unreachable!

def simpIfLocalDecl (mvarId : MVarId) (fvarId : FVarId) : MetaM (FVarId × MVarId) := do
  if let some result ← simpLocalDecl mvarId fvarId (← getSimpContext) discharge? then
    return result
  else
    unreachable!

open Std

structure TargetSubgoal where
  mvarId      : MVarId
  condFVarIds : PArray FVarId := {}

structure State where
  hNames : List Name

abbrev M := StateRefT State MetaM

private def getNextName : M Name := do
  match (← get).hNames with
  | []    => mkFreshUserName `h
  | n::ns =>
    modify fun s => { s with hNames := ns }
    return n

private partial def splitIfTargetCore (mvarId : MVarId) (condFVarIds : PArray FVarId) : M (List TargetSubgoal) := do
  if let some cond := findIfToSplit? (← getMVarType mvarId) then
    trace[Meta.splitIf] "splitting on {cond}"
    let (s₁, s₂) ← byCases mvarId cond (← getNextName)
    let (progress₁, ss₁) ← recurse s₁
    let (progress₂, ss₂) ← recurse s₂
    if progress₁ || progress₂ then
      return ss₁ ++ ss₂
    else
      return [{ mvarId, condFVarIds }]
  else
    return [{ mvarId, condFVarIds }]
where
  recurse (s : ByCasesSubgoal) : M (Bool × List TargetSubgoal) := do
    let mvarId ← simpIfTarget s.mvarId
    if mvarId == s.mvarId then
      return (false, [{ mvarId, condFVarIds }])
    else
      return (true, (← splitIfTargetCore mvarId (condFVarIds.push s.fvarId)))

structure LocalDeclSubgoal where
  mvarId      : MVarId
  fvarId      : FVarId
  condFVarIds : PArray FVarId := {}

private partial def splitIfLocalDeclCore (mvarId : MVarId) (fvarId : FVarId) (condFVarIds : PArray FVarId) : M (List LocalDeclSubgoal) :=
  withMVarContext mvarId do
  if let some cond := findIfToSplit? (← getLocalDecl fvarId).type then
    let (s₁, s₂) ← byCases mvarId cond (← getNextName)
    let (progress₁, ss₁) ← recurse s₁
    let (progress₂, ss₂) ← recurse s₂
    if progress₁ || progress₂ then
      return ss₁ ++ ss₂
    else
      return [{ mvarId, fvarId, condFVarIds }]
  else
    return [{ mvarId, fvarId, condFVarIds }]
where
  recurse (s : ByCasesSubgoal) : M (Bool × List LocalDeclSubgoal) := do
    let (fvarId', mvarId) ← simpIfLocalDecl s.mvarId fvarId
    if mvarId == s.mvarId then
      return (false, [{ mvarId, fvarId, condFVarIds }])
    else
      return (true, (← splitIfLocalDeclCore mvarId fvarId' (condFVarIds.push s.fvarId)))

structure Subgoal where
  mvarId      : MVarId
  fvarIds     : PArray FVarId := {}
  condFVarIds : PArray FVarId := {}

def splitIfGoalCore (mvarId : MVarId) (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[]) : M (List Subgoal) := do
  let mut ss ← goTarget
  for fvarId in fvarIdsToSimp do
    ss ← goLocalDecl ss fvarId
  return ss
where
  goTarget : M (List Subgoal) := do
    let mvarId ← simpIfTarget mvarId
    let ss ← splitIfTargetCore mvarId {}
    ss.mapM fun s => { s with : Subgoal }
  goLocalDecl (ss : List Subgoal) (fvarId : FVarId) : M (List Subgoal) := do
    let sss ← ss.mapM fun s => do
      let (fvarId, mvarId) ← simpIfLocalDecl s.mvarId fvarId
      let ss' ← splitIfLocalDeclCore mvarId fvarId s.condFVarIds
      ss'.mapM fun s' => { mvarId := s'.mvarId, fvarIds := s.fvarIds.push s'.fvarId, condFVarIds := s'.condFVarIds : Subgoal }
    return sss.join

end SplitIf

def splitIfGoal (mvarId : MVarId) (simplifyTarget : Bool := true) (fvarIdsToSimp : Array FVarId := #[]) (hNames : List Name := []) : MetaM (List SplitIf.Subgoal) := do
  SplitIf.splitIfGoalCore mvarId simplifyTarget fvarIdsToSimp |>.run' { hNames }

end Lean.Meta
