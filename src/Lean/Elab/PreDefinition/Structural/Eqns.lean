/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Eqns
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Apply
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Eqns
import Lean.Elab.PreDefinition.FixedParams
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab
open Meta
open Eqns

namespace Structural

structure EqnInfo extends EqnInfoCore where
  recArgPos : Nat
  declNames : Array Name
  fixedParamPerms : FixedParamPerms
  deriving Inhabited

private partial def mkProof (declName : Name) (type : Expr) : MetaM Expr := do
  trace[Elab.definition.structural.eqns] "proving: {type}"
  withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let (_, mvarId) ← main.mvarId!.intros
    unless (← tryURefl mvarId) do -- catch easy cases
      go (← deltaLHS mvarId)
    instantiateMVars main
where
  go (mvarId : MVarId) : MetaM Unit := do
    trace[Elab.definition.structural.eqns] "step\n{MessageData.ofGoal mvarId}"
    if (← tryURefl mvarId) then
      return ()
    else if (← tryContradiction mvarId) then
      return ()
    else if let some mvarId ← whnfReducibleLHS? mvarId then
      go mvarId
    else if let some mvarId ← simpMatch? mvarId then
      go mvarId
    else if let some mvarId ← simpIf? mvarId then
      go mvarId
    else
      let ctx ← Simp.mkContext
      match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
      | TacticResultCNM.closed => return ()
      | TacticResultCNM.modified mvarId => go mvarId
      | TacticResultCNM.noChange =>
        if let some mvarId ← deltaRHS? mvarId declName then
          go mvarId
        else if let some mvarIds ← casesOnStuckLHS? mvarId then
          mvarIds.forM go
        else if let some mvarIds ← splitTarget? mvarId then
          mvarIds.forM go
        else
          throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"

def mkEqns (info : EqnInfo) : MetaM (Array Name) :=
  withOptions (tactic.hygienic.set · false) do
  let eqnTypes ← withNewMCtxDepth <| lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
    let us := info.levelParams.map mkLevelParam
    let target ← mkEq (mkAppN (Lean.mkConst info.declName us) xs) body
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    mkEqnTypes info.declNames goal.mvarId!
  let baseName := info.declName
  let mut thmNames := #[]
  for h : i in [: eqnTypes.size] do
    let type := eqnTypes[i]
    trace[Elab.definition.structural.eqns] "eqnType {i}: {type}"
    let name := (Name.str baseName eqnThmSuffixBase).appendIndexAfter (i+1)
    thmNames := thmNames.push name
    -- determinism: `type` should be independent of the environment changes since `baseName` was
    -- added
    realizeConst baseName name (doRealize name type)
  return thmNames
where
  doRealize name type := withOptions (tactic.hygienic.set · false) do
    let value ← mkProof info.declName type
    let (type, value) ← removeUnusedEqnHypotheses type value
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension

def registerEqnsInfo (preDef : PreDefinition) (declNames : Array Name) (recArgPos : Nat)
    (fixedParamPerms : FixedParamPerms) : CoreM Unit := do
  ensureEqnReservedNamesAvailable preDef.declName
  modifyEnv fun env => eqnInfoExt.insert env preDef.declName
    { preDef with recArgPos, declNames, fixedParamPerms }

def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  if let some info := eqnInfoExt.find? (← getEnv) declName then
    mkEqns info
  else
    return none

def getUnfoldFor? (declName : Name) : MetaM (Option Name) := do
  let env ← getEnv
  Eqns.getUnfoldFor? declName fun _ => eqnInfoExt.find? env declName |>.map (·.toEqnInfoCore)

@[export lean_get_structural_rec_arg_pos]
def getStructuralRecArgPosImp? (declName : Name) : CoreM (Option Nat) := do
  let some info := eqnInfoExt.find? (← getEnv) declName | return none
  return some info.recArgPos

builtin_initialize
  registerGetEqnsFn getEqnsFor?
  registerGetUnfoldEqnFn getUnfoldFor?
  registerTraceClass `Elab.definition.structural.eqns

end Structural
end Lean.Elab
