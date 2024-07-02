/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Cases
import Lean.Meta.Tactic.Simp.Main

namespace Lean.Meta

inductive SplitKind where
  | ite | match | both

def SplitKind.considerIte : SplitKind → Bool
  | .ite | .both => true
  | _ => false

def SplitKind.considerMatch : SplitKind → Bool
  | .match | .both => true
  | _ => false

namespace FindSplitImpl

structure Context where
  exceptionSet : ExprSet := {}
  kind : SplitKind := .both

unsafe abbrev FindM := ReaderT Context $ StateT (PtrSet Expr) MetaM

private def isCandidate (env : Environment) (ctx : Context) (e : Expr) : Bool := Id.run do
  if ctx.exceptionSet.contains e then
    return false
  if ctx.kind.considerIte && (e.isIte || e.isDIte) then
    return !(e.getArg! 1 5).hasLooseBVars
  if ctx.kind.considerMatch then
    if let some info := isMatcherAppCore? env e then
      let args := e.getAppArgs
      for i in [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs] do
        if args[i]!.hasLooseBVars then
          return false
      return true
  return false

@[inline] unsafe def checkVisited (e : Expr) : OptionT FindM Unit := do
  if (← get).contains e then
    failure
  modify fun s => s.insert e

unsafe def visit (e : Expr) : OptionT FindM Expr := do
  checkVisited e
  if isCandidate (← getEnv) (← read) e then
    return e
  else
    -- We do not look for split candidates in proofs.
    unless e.hasLooseBVars do
      if (← isProof e) then
        failure
    match e with
    | .lam _ _ b _ | .proj _ _ b -- We do not look for split candidates in the binder of lambdas.
    | .mdata _ b       => visit b
    | .forallE _ d b _ => visit d <|> visit b -- We want to look for candidates at `A → B`
    | .letE _ _ v b _  => visit v <|> visit b
    | .app ..          => visitApp? e
    | _                => failure
where
  visitApp? (e : Expr) : FindM (Option Expr) :=
    e.withApp fun f args => do
    let info ← getFunInfo f
    for u : i in [0:args.size] do
      let arg := args[i]
      if h : i < info.paramInfo.size then
        let info := info.paramInfo[i]
        unless info.isProp do
          if info.isExplicit then
            let some found ← visit arg | pure ()
            return found
      else
        let some found ← visit arg | pure ()
        return found
    visit f

end FindSplitImpl

/-- Return an `if-then-else` or `match-expr` to split. -/
partial def findSplit? (e : Expr) (kind : SplitKind := .both) (exceptionSet : ExprSet := {}) : MetaM (Option Expr) := do
  go (← instantiateMVars e)
where
  go (e : Expr) : MetaM (Option Expr) := do
    if let some target ← find? e then
      if target.isIte || target.isDIte then
        let cond := target.getArg! 1 5
        -- Try to find a nested `if` in `cond`
        return (← go cond).getD target
      else
        return some target
    else
      return none

  find? (e : Expr) : MetaM (Option Expr) := do
    let some candidate ← unsafe FindSplitImpl.visit e { kind, exceptionSet } |>.run' mkPtrSet
      | return none
    trace[split.debug] "candidate:{indentExpr candidate}"
    return some candidate

/-- Return the condition and decidable instance of an `if` expression to case split. -/
private partial def findIfToSplit? (e : Expr) : MetaM (Option (Expr × Expr)) := do
  if let some iteApp ← findSplit? e .ite then
    let cond := iteApp.getArg! 1 5
    let dec := iteApp.getArg! 2 5
    return (cond, dec)
  else
    return none

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
  Simp.mkContext
    (simpTheorems  := #[s])
    (congrTheorems := (← getSimpCongrTheorems))
    (config        := { Simp.neutralConfig with dsimp := false })

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

def splitIfAt? (mvarId : MVarId) (e : Expr) (hName? : Option Name) : MetaM (Option (ByCasesSubgoal × ByCasesSubgoal)) := mvarId.withContext do
  let e ← instantiateMVars e
  if let some (cond, decInst) ← findIfToSplit? e then
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
      trace[split.failure] "`split` tactic failed to simplify target using new hypotheses Goals:\n{mvarId₁}\n{mvarId₂}"
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
        trace[split.failure] "`split` tactic failed to simplify target using new hypotheses Goals:\n{mvarId₁}\n{mvarId₂}"
        return none
      else
        return some (mvarId₁, mvarId₂)
    else
      return none

builtin_initialize registerTraceClass `Meta.Tactic.splitIf

end Lean.Meta
