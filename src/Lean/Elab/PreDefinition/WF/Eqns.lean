/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.Tactic.Rewrite
import Lean.Meta.Tactic.Split
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Eqns
import Lean.Meta.ArgsPacker.Basic
import Init.Data.Array.Basic
import Init.Internal.Order.Basic

namespace Lean.Elab.WF
open Meta
open Eqns

structure EqnInfo extends EqnInfoCore where
  declNames       : Array Name
  declNameNonRec  : Name
  fixedPrefixSize : Nat
  argsPacker      : ArgsPacker
  deriving Inhabited


builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ← mkMapDeclarationExtension

def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name) (fixedPrefixSize : Nat)
    (argsPacker : ArgsPacker) : MetaM Unit := do
  preDefs.forM fun preDef => ensureEqnReservedNamesAvailable preDef.declName
  /-
  See issue #2327.
  Remark: we could do better for mutual declarations that mix theorems and definitions. However, this is a rare
  combination, and we would have add support for it in the equation generator. I did not check which assumptions are made there.
  -/
  unless preDefs.all fun p => p.kind.isTheorem do
    unless (← preDefs.allM fun p => isProp p.type) do
      let declNames := preDefs.map (·.declName)
      modifyEnv fun env =>
        preDefs.foldl (init := env) fun env preDef =>
          eqnInfoExt.insert env preDef.declName { preDef with
            declNames, declNameNonRec, fixedPrefixSize, argsPacker }

private partial def deltaLHSUntilFix (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, _) := target.eq? | throwTacticEx `deltaLHSUntilFix mvarId "equality expected"
  if lhs.isAppOf ``WellFounded.fix then
    return mvarId
  else
    deltaLHSUntilFix (← deltaLHS mvarId)

private def rwFixEq (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | unreachable!
  let h ←
    if lhs.isAppOf ``WellFounded.fix then
      pure <| mkAppN (mkConst ``WellFounded.fix_eq lhs.getAppFn.constLevels!) lhs.getAppArgs
    else
      throwTacticEx `rwFixEq mvarId "expected fixed-point application"
  let some (_, _, lhsNew) := (← inferType h).eq? | unreachable!
  let targetNew ← mkEq lhsNew rhs
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
  mvarId.assign (← mkEqTrans h mvarNew)
  return mvarNew.mvarId!

/-- Generate the "unfold" lemma for `declName`. -/
partial def mkUnfoldEq (declName : Name) (info : EqnInfo) : MetaM Name := withLCtx {} {} do
  withOptions (tactic.hygienic.set · false) do
    let baseName := declName
    lambdaTelescope info.value fun xs body => do
      let us := info.levelParams.map mkLevelParam
      let type ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
      let goal ← withNewMCtxDepth do
        let goal ← mkFreshExprSyntheticOpaqueMVar type
        let mvarId := goal.mvarId!
        let mvarId ← deltaLHSUntilFix mvarId
        let mvarId ← rwFixEq mvarId
        go mvarId
        instantiateMVars goal
      let type ← mkForallFVars xs type
      let value ← mkLambdaFVars xs goal
      let name := Name.str baseName unfoldThmSuffix
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := info.levelParams
      }
      return name
  where
  /--
  Cf. the similar code in `mkEqnProof` for equational lemmas.
  -/
  go (mvarId : MVarId) : MetaM Unit := do
    trace[Elab.definition.eqns] "step\n{MessageData.ofGoal mvarId}"
    if ← withAtLeastTransparency .all (tryURefl mvarId) then
      return ()
    else if (← tryContradiction mvarId) then
      return ()
    else if let some mvarId ← simpMatch? mvarId then
      go mvarId
    else if let some mvarId ← simpIf? mvarId then
      go mvarId
    else if let some mvarId ← whnfReducibleLHS? mvarId then
      go mvarId
    else
      let ctx ← Simp.mkContext (config := { dsimp := false })
      match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
      | TacticResultCNM.closed => return ()
      | TacticResultCNM.modified mvarId => go mvarId
      | TacticResultCNM.noChange =>
        if let some mvarIds ← casesOnStuckLHS? mvarId then
          mvarIds.forM go
        else if let some mvarIds ← splitTarget? mvarId then
          mvarIds.forM go
        else
          throwError "failed to generate unfolding theorem for '{declName}'\n{MessageData.ofGoal mvarId}"


def getUnfoldFor? (declName : Name) : MetaM (Option Name) := do
  let name := Name.str declName unfoldThmSuffix
  let env ← getEnv
  if env.contains name then return name
  let some info := eqnInfoExt.find? env declName | return none
  return some (← mkUnfoldEq declName info)

def getEqnsFor? (declName : Name) : MetaM (Option (Array Name)) := do
  if let some _ := eqnInfoExt.find? (← getEnv) declName then
    mkEqns declName
  else
    return none

builtin_initialize
  registerGetEqnsFn getEqnsFor?
  registerGetUnfoldEqnFn getUnfoldFor?

end Lean.Elab.WF
