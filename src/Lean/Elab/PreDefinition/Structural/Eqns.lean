/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Meta.Basic
public import Lean.Elab.PreDefinition.Eqns
public import Lean.Elab.PreDefinition.FixedParams
import Lean.Meta.Eqns
import Lean.Meta.Tactic.Split
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Apply
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Meta.Match.MatchEqs
import Lean.Meta.Tactic.Rewrite

namespace Lean.Elab
open Meta
open Eqns

namespace Structural

public structure EqnInfo extends EqnInfoCore where
  recArgPos : Nat
  declNames : Array Name
  fixedParamPerms : FixedParamPerms
  deriving Inhabited

private partial def mkProof (declName : Name) (type : Expr) : MetaM Expr := do
  withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} proving:{indentExpr type}") do
    prependError m!"failed to generate equational theorem for `{.ofConstName declName}`" do
    withNewMCtxDepth do
      let main ← mkFreshExprSyntheticOpaqueMVar type
      let (_, mvarId) ← main.mvarId!.intros
      unless (← tryURefl mvarId) do -- catch easy cases
        goUnfold (← deltaLHS mvarId)
      instantiateMVars main
where
  goUnfold (mvarId : MVarId) : MetaM Unit := do
    withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} go2:\n{MessageData.ofGoal mvarId}") do
    let mvarId' ← mvarId.withContext do
      -- This should now be headed by `.brecOn`
      let goal ← mvarId.getType
      let some (α, lhs, rhs) := goal.eq? | throwError "goal not an equality\n{MessageData.ofGoal mvarId}"
      let brecOn := lhs.getAppFn
      unless brecOn.isConst do
        throwError "goal not headed by `.brecOn`\n{MessageData.ofGoal mvarId}"
      let brecOnName := brecOn.constName!
      unless Name.isSuffixOf `brecOn brecOnName do
        throwError "goal not headed by `.brecOn`\n{MessageData.ofGoal mvarId}"
      let brecOnThmName := brecOnName.str "eq"
      unless (← hasConst brecOnThmName) do
        throwError "no theorem `{brecOnThmName}`\n{MessageData.ofGoal mvarId}"
      -- We don't just `← inferType eqThmApp` as that beta-reduces more than we want
      let eqThmType ← inferType (mkConst brecOnThmName brecOn.constLevels!)
      let eqThmArity ← forallTelescope eqThmType fun xs _ => return xs.size
      let mut eqThmApp := mkAppN (mkConst brecOnThmName brecOn.constLevels!) lhs.getAppArgs[:eqThmArity]
      let eqThmType ← instantiateForall eqThmType eqThmApp.getAppArgs[:eqThmArity]
      let some (_, _, rwRhs) := eqThmType.eq? | throwError "theorem `{brecOnThmName}` is not an equality\n{MessageData.ofGoal mvarId}"
      let recArg := rwRhs.getAppArgs.back!
      trace[Elab.definition.structural.eqns] "abstracting{inlineExpr recArg} from{indentExpr rwRhs}"
      let mvarId2 ← mvarId.define `r (← inferType recArg) recArg
      let (r, mvarId3) ← mvarId2.intro1P
      let mut rwRhs := mkApp rwRhs.appFn! (mkFVar r)
      for extraArg in lhs.getAppArgs[eqThmArity:] do
        rwRhs := mkApp rwRhs extraArg
        eqThmApp ← mkCongrFun eqThmApp extraArg
      let eqThmAppTrans := mkApp5 (mkConst ``Eq.trans goal.getAppFn.constLevels!) α lhs rwRhs rhs eqThmApp
      let [mvarId4] ← mvarId3.applyN eqThmAppTrans 1 |
        throwError "rewriting with{inlineExpr eqThmAppTrans} failed\n{MessageData.ofGoal mvarId}"
      pure mvarId4
    go mvarId'

  go (mvarId : MVarId) : MetaM Unit := do
    withTraceNode `Elab.definition.structural.eqns (return m!"{exceptEmoji ·} step:\n{MessageData.ofGoal mvarId}") do
      if (← tryURefl mvarId) then
        trace[Elab.definition.structural.eqns] "tryURefl succeeded"
        return ()
      else if (← tryContradiction mvarId) then
        trace[Elab.definition.structural.eqns] "tryContadiction succeeded"
        return ()
      else if let some mvarId ← whnfReducibleLHS? mvarId then
        trace[Elab.definition.structural.eqns] "whnfReducibleLHS succeeded"
        go mvarId
      else if let some mvarId ← simpMatch? mvarId then
        trace[Elab.definition.structural.eqns] "simpMatch? succeeded"
        go mvarId
      else if let some mvarId ← simpIf? mvarId (useNewSemantics := true) then
        trace[Elab.definition.structural.eqns] "simpIf? succeeded"
        go mvarId
      else
        let ctx ← Simp.mkContext
        match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
        | TacticResultCNM.closed =>
          trace[Elab.definition.structural.eqns] "simpTargetStar closed the goal"
        | TacticResultCNM.modified mvarId =>
          trace[Elab.definition.structural.eqns] "simpTargetStar modified the goal"
          go mvarId
        | TacticResultCNM.noChange =>
          if let some mvarId ← deltaRHS? mvarId declName then
            trace[Elab.definition.structural.eqns] "deltaRHS? succeeded"
            go mvarId
          else if let some mvarIds ← casesOnStuckLHS? mvarId then
            trace[Elab.definition.structural.eqns] "casesOnStuckLHS? succeeded"
            mvarIds.forM go
          else if let some mvarIds ← splitTarget? mvarId (useNewSemantics := true) then
            trace[Elab.definition.structural.eqns] "splitTarget? succeeded"
            mvarIds.forM go
          else
            throwError "no progress at goal\n{MessageData.ofGoal mvarId}"

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
    let value ← withoutExporting do mkProof info.declName type
    let (type, value) ← removeUnusedEqnHypotheses type value
    let type ← letToHave type
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
    inferDefEqAttr name

public builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ←
  mkMapDeclarationExtension (exportEntriesFn := fun env s _ =>
    -- Do not export for non-exposed defs
    s.filter (fun n _ => env.find? n |>.any (·.hasValue)) |>.toArray)

public def registerEqnsInfo (preDef : PreDefinition) (declNames : Array Name) (recArgPos : Nat)
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
      let value ← mkProof declName type
      let type ← mkForallFVars xs type
      let type ← letToHave type
      let value ← mkLambdaFVars xs value
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
