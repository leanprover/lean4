/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Simp.Main

namespace Lean.Meta
namespace SplitIf

/--
  Default `Simp.Context` for `simpIf` methods. It contains all congruence theorems, but
  just the rewriting rules for reducing `if` expressions. -/
def getSimpContext : MetaM Simp.Context := do
  let mut s : SimpTheorems := {}
  s ← s.addConst ``if_pos
  s ← s.addConst ``if_neg
  s ← s.addConst ``dif_pos
  s ← s.addConst ``dif_neg
  return {
    simpTheorems  := #[s]
    congrTheorems := (← getSimpCongrTheorems)
    config        := { Simp.neutralConfig with dsimp := false }
  }

/--
  Default `discharge?` function for `simpIf` methods.
  It only uses hypotheses from the local context that have `index < numIndices`.
  It is effective after a case-split.

  Remark: when `simp` goes inside binders it adds new local declarations to the
  local context. We don't want to use these local declarations since the cached result
  would depend on them (see issue #3229). `numIndices` is the size of the local
  context `decls` field before we start the simplifying the expression.

  Remark: this function is now private, and we should use `mkDischarge?`.
-/
private def discharge? (numIndices : Nat) (useDecide : Bool) : Simp.Discharge := fun prop => do
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
     if localDecl.index ≥ numIndices || localDecl.isAuxDecl then
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

def mkDischarge? (useDecide := false) : MetaM Simp.Discharge :=
  return discharge? (← getLCtx).numIndices useDecide

/-- Return the condition and decidable instance of an `if` expression to case split. -/
private partial def findIfToSplit? (e : Expr) : Option (Expr × Expr) :=
  if let some iteApp := e.find? fun e => (e.isIte || e.isDIte) && !(e.getArg! 1 5).hasLooseBVars then
    let cond := iteApp.getArg! 1 5
    let dec := iteApp.getArg! 2 5
    -- Try to find a nested `if` in `cond`
    findIfToSplit? cond |>.getD (cond, dec)
  else
    none

def splitIfAt? (mvarId : MVarId) (e : Expr) (hName? : Option Name) : MetaM (Option (ByCasesSubgoal × ByCasesSubgoal)) := do
  let e ← instantiateMVars e
  if let some (cond, decInst) := findIfToSplit? e then
    let hName ← match hName? with
      | none       => mkFreshUserName `h
      | some hName => pure hName
    trace[Meta.Tactic.splitIf] "splitting on {decInst}"
    return some (← mvarId.byCasesDec cond decInst hName)
  else
    return none

end SplitIf

open SplitIf

def simpIfTarget (mvarId : MVarId) (useDecide := false) : MetaM MVarId := do
  let mut ctx ← getSimpContext
  if let (some mvarId', _) ← simpTarget mvarId ctx {} (← mvarId.withContext <| mkDischarge? useDecide) (mayCloseGoal := false) then
    return mvarId'
  else
    unreachable!

def simpIfLocalDecl (mvarId : MVarId) (fvarId : FVarId) : MetaM MVarId := do
  let mut ctx ← getSimpContext
  if let (some (_, mvarId'), _) ← simpLocalDecl mvarId fvarId ctx {} (← mvarId.withContext <| mkDischarge?) (mayCloseGoal := false) then
    return mvarId'
  else
    unreachable!

def splitIfTarget? (mvarId : MVarId) (hName? : Option Name := none) : MetaM (Option (ByCasesSubgoal × ByCasesSubgoal)) := commitWhenSome? do
  if let some (s₁, s₂) ← splitIfAt? mvarId (← mvarId.getType) hName? then
    let mvarId₁ ← simpIfTarget s₁.mvarId
    let mvarId₂ ← simpIfTarget s₂.mvarId
    if s₁.mvarId == mvarId₁ && s₂.mvarId == mvarId₂ then
      return none
    else
      return some ({ s₁ with mvarId := mvarId₁ }, { s₂ with mvarId := mvarId₂ })
  else
    return none

def splitIfLocalDecl? (mvarId : MVarId) (fvarId : FVarId) (hName? : Option Name := none) : MetaM (Option (MVarId × MVarId)) := commitWhenSome? do
  mvarId.withContext do
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
