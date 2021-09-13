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

/--
  Default `Simp.Context` for `simpIf` methods. It contains all congruence lemmas, but
  just the rewriting rules for reducing `if` expressions. -/
def getSimpContext : MetaM Simp.Context :=
  ext.get

/--
  Default `discharge?` function for `simpIf` methods.
  It only uses hypotheses from the local context. It is effective
  after a case-split. -/
def discharge? (useDecide := false) : Simp.Discharge := fun prop => do
  let prop ← instantiateMVars prop
  trace[Meta.Tactic.splitIf] "discharge? {prop}, {prop.notNot?}"
  if useDecide then
    let prop ← instantiateMVars prop
    if !prop.hasFVar && !prop.hasMVar then
      let d ← mkDecide prop
      let r ← withDefault <| whnf d
      if r.isConstOf ``true then
        return some <| mkApp3 (mkConst ``of_decide_eq_true) prop d.appArg! (← mkEqRefl (mkConst ``true))
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

/-- Return the condition of an `if` expression to case split. -/
partial def findIfToSplit? (e : Expr) : Option Expr :=
  if let some iteApp := e.find? fun e => (e.isIte || e.isDIte) && !(e.getArg! 1 5).hasLooseBVars then
    let cond := iteApp.getArg! 1 5
    -- Try to find a nested `if` in `cond`
    findIfToSplit? cond |>.getD cond
  else
    none

def splitIfAt? (mvarId : MVarId) (e : Expr) (hName? : Option Name) : MetaM (Option (ByCasesSubgoal × ByCasesSubgoal)) := do
  if let some cond := findIfToSplit? e then
    let hName ← match hName? with
      | none       => mkFreshUserName `h
      | some hName => pure hName
    trace[Meta.Tactic.splitIf] "splitting on {cond}"
    return some (← byCases mvarId cond hName)
  else
    return none

end SplitIf

open SplitIf

def simpIfTarget (mvarId : MVarId) (useDecide := false) : MetaM MVarId := do
  let mut ctx ← getSimpContext
  if let some mvarId' ← simpTarget mvarId ctx (discharge? useDecide) then
    return mvarId'
  else
    unreachable!

def simpIfLocalDecl (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId := do
  let mut ctx ← getSimpContext
  if let some (_, mvarId') ← simpLocalDecl mvarId fvarId ctx discharge? then
    return mvarId'
  else
    unreachable!

def splitIfTarget? (mvarId : MVarId) (hName? : Option Name := none) : MetaM (Option (ByCasesSubgoal × ByCasesSubgoal)) := commitWhenSome? do
  if let some (s₁, s₂) ← splitIfAt? mvarId (← getMVarType mvarId) hName? then
    let mvarId₁ ← simpIfTarget s₁.mvarId
    let mvarId₂ ← simpIfTarget s₂.mvarId
    if s₁.mvarId == mvarId₁ && s₂.mvarId == mvarId₂ then
      return none
    else
      return some ({ s₁ with mvarId := mvarId₁ }, { s₂ with mvarId := mvarId₂ })
  else
    return none

def splitIfLocalDecl? (mvarId : MVarId) (fvarId : FVarId) (hName? : Option Name := none) : MetaM (Option (MVarId × MVarId)) := commitWhenSome? do
  withMVarContext mvarId do
    if let some (s₁, s₂) ← splitIfAt? mvarId (← inferType (mkFVar fvarId)) hName? then
      let mvarId₁ ← simpIfLocalDecl s₁.mvarId fvarId
      let mvarId₂ ← simpIfLocalDecl s₂.mvarId fvarId
      if s₁.mvarId == mvarId₁ && s₂.mvarId == mvarId₂ then
        return none
      else
        return some (mvarId₁, mvarId₂)
    else
      return none

builtin_initialize registerTraceClass `Meta.Tactic.splitIf

end Lean.Meta
