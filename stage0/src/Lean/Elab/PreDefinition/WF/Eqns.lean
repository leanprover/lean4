/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Split
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Eqns

namespace Lean.Elab.WF
open Meta
open Eqns

structure EqnInfo extends EqnInfoCore where
  declNames       : Array Name
  declNameNonRec  : Name
  fixedPrefixSize : Nat
  deriving Inhabited

private partial def deltaLHSUntilFix (mvarId : MVarId) : MetaM MVarId := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) := target.eq? | throwTacticEx `deltaLHSUntilFix mvarId "equality expected"
  if lhs.isAppOf ``WellFounded.fix then
    return mvarId
  else
    deltaLHSUntilFix (← deltaLHS mvarId)

private def rwFixEq (mvarId : MVarId) : MetaM MVarId := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) := target.eq? | unreachable!
  let h := mkAppN (mkConst ``WellFounded.fix_eq lhs.getAppFn.constLevels!) lhs.getAppArgs
  let some (_, _, lhsNew) := (← inferType h).eq? | unreachable!
  let targetNew ← mkEq lhsNew rhs
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
  assignExprMVar mvarId (← mkEqTrans h mvarNew)
  return mvarNew.mvarId!

private def hasWellFoundedFix (e : Expr) : Bool :=
  Option.isSome <| e.find? (·.isConstOf ``WellFounded.fix)

def simpMatchWF? (mvarId : MVarId) (info : EqnInfo) : MetaM (Option MVarId) := withMVarContext mvarId do
  let target ← instantiateMVars (← getMVarType mvarId)
  let targetNew ← Simp.main target (← Split.getSimpMatchContext) (methods := { pre })
  let mvarIdNew ← applySimpResultToTarget mvarId target targetNew
  if mvarId != mvarIdNew then return some mvarIdNew else return none
where
  pre (e : Expr) : SimpM Simp.Step := do
    let some app ← matchMatcherApp? e | return Simp.Step.visit { expr := e }
    if app.discrs.any hasWellFoundedFix then
      -- TODO: try to fold `WellFounded.fix` occurrences in the discriminant
      pure ()
    -- First try to reduce matcher
    match (← reduceRecMatcher? e) with
    | some e' => return Simp.Step.done { expr := e' }
    | none    =>
      match (← Simp.simpMatchCore? app e SplitIf.discharge?) with
      | some r => return r
      | none => return Simp.Step.visit { expr := e }

private partial def mkProof (declName : Name) (info : EqnInfo) (type : Expr) : MetaM Expr := do
  trace[Elab.definition.wf.eqns] "proving: {type}"
  withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let (_, mvarId) ← intros main.mvarId!
    go (← rwFixEq (← deltaLHSUntilFix mvarId))
    instantiateMVars main
where
  go (mvarId : MVarId) : MetaM Unit := do
    trace[Elab.definition.wf.eqns] "step\n{MessageData.ofGoal mvarId}"
    if (← tryURefl mvarId) then
      return ()
    else if (← tryContradiction mvarId) then
      return ()
    else if let some mvarId ← simpMatchWF? mvarId info then
      go mvarId
    else if let some mvarId ← simpIf? mvarId then
      go mvarId
    else if let some mvarId ← whnfReducibleLHS? mvarId then
      go mvarId
    else match (← simpTargetStar mvarId {}) with
      | TacticResultCNM.closed => return ()
      | TacticResultCNM.modified mvarId => go mvarId
      | TacticResultCNM.noChange =>
        if let some mvarIds ← casesOnStuckLHS? mvarId then
          mvarIds.forM go
        else if let some mvarIds ← splitTarget? mvarId then
          mvarIds.forM go
        else
          throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"

def mkEqns (declName : Name) (info : EqnInfo) : MetaM (Array Name) :=
  withOptions (tactic.hygienic.set · false) do
  let baseName := mkPrivateName (← getEnv) declName
  let eqnTypes ← withNewMCtxDepth <| lambdaTelescope info.value fun xs body => do
    let us := info.levelParams.map mkLevelParam
    let target ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    mkEqnTypes info.declNames goal.mvarId!
  let mut thmNames := #[]
  for i in [: eqnTypes.size] do
    let type := eqnTypes[i]
    trace[Elab.definition.wf.eqns] "{eqnTypes[i]}"
    let name := baseName ++ (`_eq).appendIndexAfter (i+1)
    thmNames := thmNames.push name
    let value ← mkProof declName info type
    let (type, value) ← removeUnusedEqnHypotheses type value
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
  return thmNames

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension `wfEqInfo

def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name) (fixedPrefixSize : Nat) : CoreM Unit := do
  let declNames := preDefs.map (·.declName)
  modifyEnv fun env =>
    preDefs.foldl (init := env) fun env preDef =>
      eqnInfoExt.insert env preDef.declName { preDef with declNames, declNameNonRec, fixedPrefixSize }

def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  if let some info := eqnInfoExt.find? (← getEnv) declName then
    mkEqns declName info
  else
    return none

def getUnfoldFor? (declName : Name) : MetaM (Option Name) := do
  let env ← getEnv
  Eqns.getUnfoldFor? declName fun _ => eqnInfoExt.find? env declName |>.map (·.toEqnInfoCore)

builtin_initialize
  registerGetEqnsFn getEqnsFor?
  registerGetUnfoldEqnFn getUnfoldFor?
  registerTraceClass `Elab.definition.wf.eqns

end Lean.Elab.WF
