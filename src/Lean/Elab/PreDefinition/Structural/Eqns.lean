/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Eqns
public import Lean.Meta.Tactic.Split
public import Lean.Meta.Tactic.Simp.Main
public import Lean.Meta.Tactic.Apply
public import Lean.Elab.PreDefinition.Basic
public import Lean.Elab.PreDefinition.Eqns
public import Lean.Elab.PreDefinition.FixedParams
public import Lean.Elab.PreDefinition.Structural.Basic

public section

namespace Lean.Elab
open Meta
open Eqns

namespace Structural

structure EqnInfo extends EqnInfoCore where
  recArgPos : Nat
  declNames : Array Name
  fixedParamPerms : FixedParamPerms
  deriving Inhabited

private partial def mkProof (type : Expr) : MetaM Expr := do
  withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} proving:{indentExpr type}") do
    withNewMCtxDepth do
      let main ← mkFreshExprSyntheticOpaqueMVar type
      let (_, mvarId) ← main.mvarId!.intros
      unless (← tryURefl mvarId) do -- catch easy cases
        go1 mvarId
      instantiateMVars main
where
  /--
  Step 1: Split the function body into its cases, but keeping the LHS intact, because the
  `.below`-added `match` statements and the `.rec` can quickly confuse `split`.
  -/
  go1 (mvarId : MVarId) : MetaM Unit := do
    withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} go1:\n{MessageData.ofGoal mvarId}") do
      if (← tryURefl mvarId) then
        trace[Elab.definition.structural.eqns] "tryURefl succeeded"
        return ()
      else if (← tryContradiction mvarId) then
        trace[Elab.definition.structural.eqns] "tryContadiction succeeded"
        return ()
      else if let some mvarId ← simpMatch? mvarId then
        trace[Elab.definition.structural.eqns] "simpMatch? succeeded"
        go1 mvarId
      else if let some mvarId ← simpIf? mvarId (useNewSemantics := true) then
        trace[Elab.definition.structural.eqns] "simpIf? succeeded"
        go1 mvarId
      else
        let ctx ← Simp.mkContext
        match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
        | TacticResultCNM.closed =>
          trace[Elab.definition.structural.eqns] "simpTargetStar closed the goal"
        | TacticResultCNM.modified mvarId =>
          trace[Elab.definition.structural.eqns] "simpTargetStar modified the goal"
          go1 mvarId
        | TacticResultCNM.noChange =>
          -- if let some mvarId ← deltaRHS? mvarId declName then
          --   trace[Elab.definition.structural.eqns] "deltaRHS? succeeded"
          --   go1 mvarId
          if let some mvarIds ← casesOnStuckLHS? mvarId then
            trace[Elab.definition.structural.eqns] "casesOnStuckLHS? succeeded"
            mvarIds.forM go1
          else if let some mvarIds ← splitTarget? mvarId (useNewSemantics := true) then
            trace[Elab.definition.structural.eqns] "splitTarget? succeeded"
            mvarIds.forM go1
          else
            go2 (← deltaLHS mvarId)
  /-- Step 2: Unfold the lhs to expose the recursor. -/
  go2 (mvarId : MVarId) : MetaM Unit := do
    withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} go2:\n{MessageData.ofGoal mvarId}") do
    if let some mvarId ← whnfReducibleLHS? mvarId then
      go2 mvarId
    else
      go3 mvarId
  /-- Step 3: Simplify the match and if statements on the left hand side, until we have rfl. -/
  go3 (mvarId : MVarId) : MetaM Unit := do
      withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} go3:\n{MessageData.ofGoal mvarId}") do
      if (← tryURefl mvarId) then
        trace[Elab.definition.structural.eqns] "tryURefl succeeded"
        return ()
      else if let some mvarId ← simpMatch? mvarId then
        trace[Elab.definition.structural.eqns] "simpMatch? succeeded"
        go3 mvarId
      else if let some mvarId ← simpIf? mvarId (useNewSemantics := true) then
        trace[Elab.definition.structural.eqns] "simpIf? succeeded"
        go3 mvarId
      else
        let ctx ← Simp.mkContext
        match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
        | TacticResultCNM.closed =>
          trace[Elab.definition.structural.eqns] "simpTargetStar closed the goal"
        | TacticResultCNM.modified mvarId =>
          trace[Elab.definition.structural.eqns] "simpTargetStar modified the goal"
          go1 mvarId
        | TacticResultCNM.noChange =>
          if let some mvarIds ← casesOnStuckLHS? mvarId then
            trace[Elab.definition.structural.eqns] "casesOnStuckLHS? succeeded"
            mvarIds.forM go3
          else
            go3 mvarId

def mkEqns (info : EqnInfo) : MetaM (Array Name) :=
  withOptions (tactic.hygienic.set · false) do
  let eqnTypes ← withNewMCtxDepth <| lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
    let us := info.levelParams.map mkLevelParam
    let target ← mkEq (mkAppN (Lean.mkConst info.declName us) xs) body
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    mkEqnTypes info.declNames goal.mvarId!
  let mut thmNames := #[]
  for h : i in *...eqnTypes.size do
    let type := eqnTypes[i]
    trace[Elab.definition.structural.eqns] "eqnType {i+1}: {type}"
    let name := mkEqLikeNameFor (← getEnv) info.declName s!"{eqnThmSuffixBasePrefix}{i+1}"
    thmNames := thmNames.push name
    -- determinism: `type` should be independent of the environment changes since `baseName` was
    -- added
    realizeConst info.declNames[0]! name (doRealize name type)
  return thmNames
where
  doRealize name type := withOptions (tactic.hygienic.set · false) do
    let value ← withoutExporting do mkProof type
    let (type, value) ← removeUnusedEqnHypotheses type value
    let type ← letToHave type
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
    inferDefEqAttr name

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ←
  mkMapDeclarationExtension (exportEntriesFn := fun env s _ =>
    -- Do not export for non-exposed defs
    s.filter (fun n _ => env.find? n |>.any (·.hasValue)) |>.toArray)

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

/-- Generate the "unfold" lemma for `declName`. -/
def mkUnfoldEq (declName : Name) (info : EqnInfo) : MetaM Name := do
  let name := mkEqLikeNameFor (← getEnv) info.declName unfoldThmSuffix
  realizeConst info.declNames[0]! name (doRealize name)
  return name
where
  doRealize name := withOptions (tactic.hygienic.set · false) do
    lambdaTelescope info.value fun xs body => do
      let us := info.levelParams.map mkLevelParam
      let type ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
      let goal ← mkFreshExprSyntheticOpaqueMVar type
      mkUnfoldProof declName goal.mvarId!
      let type ← mkForallFVars xs type
      let type ← letToHave type
      let value ← mkLambdaFVars xs (← instantiateMVars goal)
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := info.levelParams
      }
      inferDefEqAttr name

def getUnfoldFor? (declName : Name) : MetaM (Option Name) := do
  if let some info := eqnInfoExt.find? (← getEnv) declName then
    return some (← mkUnfoldEq declName info)
  else
    return none

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
