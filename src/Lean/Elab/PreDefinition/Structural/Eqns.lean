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
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab
open Meta
open Eqns

namespace Structural

structure EqnInfo extends EqnInfoCore where
  recArgPos : Nat
  declNames : Array Name
  numFixed  : Nat
  deriving Inhabited

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension

private partial def mkProof (declName : Name) (unfold : MVarId → MetaM MVarId) (type : Expr) : MetaM Expr := do
  trace[Elab.definition.structural.eqns] "proving: {type}"
  withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let (_, mvarId) ← main.mvarId!.intros
    unless (← tryURefl mvarId) do -- catch easy cases
      go (← unfold mvarId)
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
    else match (← simpTargetStar mvarId {} (simprocs := {})).1 with
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

private partial def mkUnfoldProof (declName : Name) (type : Expr) : MetaM Expr := do
  mkProof declName deltaLHS type


/-- Generate the "unfold" lemma for `declName`. -/
def mkUnfoldEq (declName : Name) (info : EqnInfo) : MetaM Name := withLCtx {} {} do
  withOptions (tactic.hygienic.set · false) do
    let baseName := declName
    lambdaTelescope info.value fun xs body => do
      let us := info.levelParams.map mkLevelParam
      let type ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
      let value ← mkUnfoldProof declName type
      let type ← mkForallFVars xs type
      let value ← mkLambdaFVars xs value
      let name := Name.str baseName unfoldThmSuffix
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := info.levelParams
      }
      return name

def getUnfoldFor? (declName : Name) : MetaM (Option Name) := do
  if let some info := eqnInfoExt.find? (← getEnv) declName then
    return some (← mkUnfoldEq declName info)
  else
    return none

private def rwWithUnfold (declName : Name) (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let .some unfold ← getUnfoldEqnFor? declName | throwError "rwWithUnfold: No unfold lemma?"
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | unreachable!
  let h := mkAppN (mkConst unfold lhs.getAppFn.constLevels!) lhs.getAppArgs
  let some (_, _, lhsNew) := (← inferType h).eq? | unreachable!
  let targetNew ← mkEq lhsNew rhs
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
  mvarId.assign (← mkEqTrans h mvarNew)
  return mvarNew.mvarId!

private partial def mkEqnProof (declName : Name) (type : Expr) : MetaM Expr := do
  mkProof declName (rwWithUnfold declName) type

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
    let value ← mkEqnProof info.declName type
    let (type, value) ← removeUnusedEqnHypotheses type value
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
  return thmNames


def registerEqnsInfo (preDef : PreDefinition) (declNames : Array Name) (recArgPos : Nat)
    (numFixed : Nat) : CoreM Unit := do
  ensureEqnReservedNamesAvailable preDef.declName
  modifyEnv fun env => eqnInfoExt.insert env preDef.declName
    { preDef with recArgPos, declNames, numFixed }

def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  if let some info := eqnInfoExt.find? (← getEnv) declName then
    mkEqns info
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
