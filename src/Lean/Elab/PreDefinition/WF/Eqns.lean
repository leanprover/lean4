/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Tactic.Rewrite
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Eqns

namespace Lean.Elab.WF
open Meta
open Eqns

structure EqnInfo where
  declNames      : Array Name
  levelParams    : List Name
  type           : Expr
  value          : Expr
  declNameNonRec : Name
  deriving Inhabited

private partial def deltaLHSUntilFix (mvarId : MVarId) : MetaM MVarId := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) ← target.eq? | throwTacticEx `deltaLHSUntilFix mvarId "equality expected"
  if lhs.isAppOf ``WellFounded.fix then
    return mvarId
  else
    deltaLHSUntilFix (← deltaLHS mvarId)

private def rwFixEq (mvarId : MVarId) : MetaM MVarId := withMVarContext mvarId do
  let target ← getMVarType' mvarId
  let some (_, lhs, rhs) ← target.eq? | unreachable!
  let h := mkAppN (mkConst ``WellFounded.fix_eq lhs.getAppFn.constLevels!) lhs.getAppArgs
  let r ← rewrite mvarId target h
  replaceTargetEq mvarId r.eNew r.eqProof

private partial def mkProof (declName : Name) (type : Expr) : MetaM Expr := do
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
    else if let some mvarId ← simpMatch? mvarId then
      go mvarId
    else if let some mvarId ← simpIf? mvarId then
      go mvarId
    else if let some mvarId ← whnfReducibleLHS? mvarId then
      go mvarId
    else if let some mvarIds ← casesOnStuckLHS? mvarId then
      mvarIds.forM go
    else
      throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"

def mkEqns (declName : Name) (info : EqnInfo) : MetaM (Array Name) :=
  withOptions (tactic.hygienic.set . false) do
  let baseName := Eqns.mkBaseNameFor (← getEnv) declName
  -- let unfoldLemma ← mkUnfoldLemma declName info baseName
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
    let value ← mkProof declName type
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
  return thmNames

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension `wfEqInfo

def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name) : CoreM Unit := do
  let declNames := preDefs.map (·.declName)
  modifyEnv fun env =>
    preDefs.foldl (init := env) fun env preDef =>
      eqnInfoExt.insert env preDef.declName { preDef with declNames, declNameNonRec }

def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  let env ← getEnv
  if let some eqs := eqnsExt.getState env |>.map.find? declName then
    return some eqs
  else if let some info := eqnInfoExt.find? env declName then
    let eqs ← mkEqns declName info
    modifyEnv fun env => eqnsExt.modifyState env fun s => { s with map := s.map.insert declName eqs }
    return some eqs
  else
    return none

builtin_initialize
  registerGetEqnsFn getEqnsFor?
  registerTraceClass `Elab.definition.wf.eqns

end Lean.Elab.WF
