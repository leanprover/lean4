/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.MatchEqs
import Lean.Meta.Tactic.Generalize

namespace Lean.Meta
namespace Split

private def getSimpMatchContext : MetaM Simp.Context :=
   return {
      simpLemmas    := {}
      congrLemmas   := (← getCongrLemmas)
      config.zeta   := false
      config.beta   := false
      config.eta    := false
      config.iota   := false
      config.proj   := false
      config.decide := false
   }

def simpMatch (e : Expr) : MetaM Simp.Result := do
  Simp.main e (← getSimpMatchContext) (methods := { pre })
where
  pre (e : Expr) : SimpM Simp.Step := do
    let some app ← matchMatcherApp? e | return Simp.Step.visit { expr := e }
    -- First try to reduce matcher
    match (← reduceRecMatcher? e) with
    | some e' => return Simp.Step.done { expr := e' }
    | none    =>
      for matchEq in (← Match.getEquationsFor app.matcherName).eqnNames do
        -- Try lemma
        match (← withReducible <| Simp.tryLemma? e { proof := mkConst matchEq, name? := some matchEq } SplitIf.discharge?) with
        | none   => pure ()
        | some r => return Simp.Step.done r
      return Simp.Step.visit { expr := e }

def simpMatchTarget (mvarId : MVarId) : MetaM MVarId := withMVarContext mvarId do
  let target ← instantiateMVars (← getMVarType mvarId)
  let r ← simpMatch target
  applySimpResultToTarget mvarId target r

private def simpMatchCore (matchDeclName : Name) (matchEqDeclName : Name) (e : Expr) : MetaM Simp.Result := do
  Simp.main e (← getSimpMatchContext) (methods := { pre })
where
  pre (e : Expr) : SimpM Simp.Step := do
    if e.isAppOf matchDeclName then
      -- First try to reduce matcher
      match (← reduceRecMatcher? e) with
      | some e' => return Simp.Step.done { expr := e' }
      | none    =>
      -- Try lemma
      match (← withReducible <| Simp.tryLemma? e { proof := mkConst matchEqDeclName, name? := matchEqDeclName } SplitIf.discharge?) with
      | none => return Simp.Step.visit { expr := e }
      | some r => return Simp.Step.done r
    else
      return Simp.Step.visit { expr := e }

private def simpMatchTargetCore (mvarId : MVarId) (matchDeclName : Name) (matchEqDeclName : Name) : MetaM MVarId := do
  withMVarContext mvarId do
    let target ← instantiateMVars (← getMVarType mvarId)
    let r ← simpMatchCore matchDeclName matchEqDeclName target
    match r.proof? with
    | some proof => replaceTargetEq mvarId r.expr proof
    | none => replaceTargetDefEq mvarId r.expr

private def generalizeMatchDiscrs (mvarId : MVarId) (discrs : Array Expr) : MetaM (Array FVarId × MVarId) := do
  if discrs.all (·.isFVar) then
    return (discrs.map (·.fvarId!), mvarId)
  else
    let args ← discrs.mapM fun d => return { expr := d, hName? := (← mkFreshUserName `h) : GeneralizeArg }
    let (fvarIds, mvarId) ← generalize mvarId args
    return (fvarIds[:discrs.size], mvarId)

def applyMatchSplitter (mvarId : MVarId) (matcherDeclName : Name) (us : Array Level) (params : Array Expr) (discrs : Array Expr) : MetaM (List MVarId) := do
  let (discrFVarIds, mvarId) ← generalizeMatchDiscrs mvarId discrs
  let (reverted, mvarId) ← revert mvarId discrFVarIds (preserveOrder := true)
  let (discrFVarIds, mvarId) ← introNP mvarId discrFVarIds.size
  let numExtra := reverted.size - discrFVarIds.size
  let discrs := discrFVarIds.map mkFVar
  let some info ← getMatcherInfo? matcherDeclName | throwError "'applyMatchSplitter' failed, '{matcherDeclName}' is not a 'match' auxiliary declaration."
  let matchEqns ← Match.getEquationsFor matcherDeclName
  withMVarContext mvarId do
    let motive ← mkLambdaFVars discrs (← getMVarType mvarId)
    -- Fix universe
    let mut us := us
    if let some uElimPos := info.uElimPos? then
      -- Set universe elimination level to zero (Prop).
      us := us.set! uElimPos levelZero
    let splitter := mkAppN (mkConst matchEqns.splitterName us.toList) params
    let splitter := mkAppN (mkApp splitter motive) discrs
    check splitter -- TODO
    let mvarIds ← apply mvarId splitter
    let (_, mvarIds) ← mvarIds.foldlM (init := (0, [])) fun (i, mvarIds) mvarId => do
      let numParams := matchEqns.splitterAltNumParams[i]
      let (_, mvarId) ← introN mvarId numParams
      let (_, mvarId) ← introNP mvarId numExtra
      return (i+1, mvarId::mvarIds)
    return mvarIds.reverse

def splitMatch (mvarId : MVarId) (e : Expr) : MetaM (List MVarId) := do
  let some app ← matchMatcherApp? e | throwError "match application expected"
  let matchEqns ← Match.getEquationsFor app.matcherName
  let mvarIds ← applyMatchSplitter mvarId app.matcherName app.matcherLevels app.params app.discrs
  let (_, mvarIds) ← mvarIds.foldlM (init := (0, [])) fun (i, mvarIds) mvarId => do
    let mvarId ← simpMatchTargetCore mvarId app.matcherName matchEqns.eqnNames[i]
    return (i+1, mvarId::mvarIds)
  return mvarIds.reverse

/-- Return an `if-then-else` or `match-expr` to split. -/
partial def findSplit? (env : Environment) (e : Expr) : Option Expr :=
  if let some target := e.find? isCandidate then
    if e.isIte || e.isDIte then
      let cond := target.getArg! 1 5
      -- Try to find a nested `if` in `cond`
      findSplit? env cond |>.getD target
    else
      some target
  else
    none
where
  isCandidate (e : Expr) : Bool := do
    if e.isIte || e.isDIte then
      !(e.getArg! 1 5).hasLooseBVars
    else if let some info := isMatcherAppCore? env e then
      let args := e.getAppArgs
      for i in [info.getFirstDiscrPos : info.getFirstDiscrPos + info.numDiscrs] do
        if args[i].hasLooseBVars then
          return false
      return true
    else
      false

end Split

open Split

def splitTarget? (mvarId : MVarId) : MetaM (Option (List MVarId)) := commitWhenSome? do
  if let some e := findSplit? (← getEnv) (← instantiateMVars (← getMVarType mvarId)) then
    if e.isIte || e.isDIte then
      return (← splitIfTarget? mvarId).map fun (s₁, s₂) => [s₁.mvarId, s₂.mvarId]
    else
      splitMatch mvarId e
  else
    trace[Meta.Tactic.split] "did not find term to split\n{MessageData.ofGoal mvarId}"
    return none

def splitLocalDecl? (mvarId : MVarId) (fvarId : FVarId) : MetaM (Option (List MVarId)) := commitWhenSome? do
  withMVarContext mvarId do
    if let some e := findSplit? (← getEnv) (← instantiateMVars (← inferType (mkFVar fvarId))) then
      if e.isIte || e.isDIte then
        return (← splitIfLocalDecl? mvarId fvarId).map fun (mvarId₁, mvarId₂) => [mvarId₁, mvarId₂]
      else
        let (fvarIds, mvarId) ← revert mvarId #[fvarId]
        let num := fvarIds.size
        let mvarIds ← splitMatch mvarId e
        let mvarIds ← mvarIds.mapM fun mvarId => return (← introNP mvarId num).2
        return some mvarIds
    else
      return none

builtin_initialize registerTraceClass `Meta.Tactic.split

end Lean.Meta
