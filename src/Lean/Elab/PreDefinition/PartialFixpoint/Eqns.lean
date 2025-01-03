/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.Tactic.Conv
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Split
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Eqns
import Lean.Meta.ArgsPacker.Basic
import Init.Data.Array.Basic
import Init.Internal.Order.Basic

namespace Lean.Elab.PartialFixpoint
open Meta
open Eqns

structure EqnInfo extends EqnInfoCore where
  declNames       : Array Name
  declNameNonRec  : Name
  fixedPrefixSize : Nat
  deriving Inhabited

private def deltaLHSUntilFix (declName declNameNonRec : Name) (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | throwTacticEx `deltaLHSUntilFix mvarId "equality expected"
  let lhs' ← deltaExpand lhs fun n => n == declName || n == declNameNonRec
  mvarId.replaceTargetDefEq (← mkEq lhs' rhs)

partial def rwFixUnder (lhs : Expr) : MetaM Expr := do
  if lhs.isAppOfArity ``Order.fix 4 then
    return mkAppN (mkConst ``Order.fix_eq lhs.getAppFn.constLevels!) lhs.getAppArgs
  else if lhs.isApp then
    let h ← rwFixUnder lhs.appFn!
    mkAppM ``congrFun #[h, lhs.appArg!]
  else if lhs.isProj then
    let f := mkLambda `p .default (← inferType lhs.projExpr!) (lhs.updateProj! (.bvar 0))
    let h ← rwFixUnder lhs.projExpr!
    mkAppM ``congrArg #[f, h]
  else
    throwError "rwFixUnder: unexpected expression {lhs}"

private def rwFixEq (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let mut mvarId := mvarId
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | unreachable!
  let h ← rwFixUnder lhs
  let some (_, _, lhsNew) := (← inferType h).eq? | unreachable!
  let targetNew ← mkEq lhsNew rhs
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
  mvarId.assign (← mkEqTrans h mvarNew)
  return mvarNew.mvarId!

private partial def mkProof (declName : Name) (declNameNonRec : Name) (type : Expr) : MetaM Expr := do
  trace[Elab.definition.partialFixpoint] "proving: {type}"
  withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let (_, mvarId) ← main.mvarId!.intros
    let mvarId ← deltaLHSUntilFix declName declNameNonRec mvarId
    let mvarId ← rwFixEq mvarId
    if ← withAtLeastTransparency .all (tryURefl mvarId) then
      instantiateMVars main
    else
      throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"

def mkEqns (declName : Name) (info : EqnInfo) : MetaM (Array Name) :=
  withOptions (tactic.hygienic.set · false) do
  let baseName := declName
  let eqnTypes ← withNewMCtxDepth <| lambdaTelescope (cleanupAnnotations := true) info.value fun xs body => do
    let us := info.levelParams.map mkLevelParam
    let target ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
    let goal ← mkFreshExprSyntheticOpaqueMVar target
    withReducible do
      mkEqnTypes info.declNames goal.mvarId!
  let mut thmNames := #[]
  for h : i in [: eqnTypes.size] do
    let type := eqnTypes[i]
    trace[Elab.definition.partialFixpoint] "{eqnTypes[i]}"
    let name := (Name.str baseName eqnThmSuffixBase).appendIndexAfter (i+1)
    thmNames := thmNames.push name
    let value ← mkProof declName info.declNameNonRec type
    let (type, value) ← removeUnusedEqnHypotheses type value
    addDecl <| Declaration.thmDecl {
      name, type, value
      levelParams := info.levelParams
    }
  return thmNames

builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension

def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name) (fixedPrefixSize : Nat) : MetaM Unit := do
  preDefs.forM fun preDef => ensureEqnReservedNamesAvailable preDef.declName
  unless preDefs.all fun p => p.kind.isTheorem do
    unless (← preDefs.allM fun p => isProp p.type) do
      let declNames := preDefs.map (·.declName)
      modifyEnv fun env =>
        preDefs.foldl (init := env) fun env preDef =>
          eqnInfoExt.insert env preDef.declName { preDef with
            declNames, declNameNonRec, fixedPrefixSize }

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

end Lean.Elab.PartialFixpoint
