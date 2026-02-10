/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.PreDefinition.FixedParams
import Init.Internal.Order.Basic
import Lean.Meta.Tactic.Delta
import Lean.Meta.Tactic.Refl

namespace Lean.Elab.PartialFixpoint
open Meta

public structure EqnInfo where
  declName    : Name
  levelParams : List Name
  type        : Expr
  value       : Expr
  declNames       : Array Name
  declNameNonRec  : Name
  fixedParamPerms : FixedParamPerms
  fixpointType    : Array PartialFixpointType
  deriving Inhabited

public builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ←
  mkMapDeclarationExtension (exportEntriesFn := fun env s _ =>
    -- Do not export for non-exposed defs
    s.filter (fun n _ => env.find? n |>.any (·.hasValue)) |>.toArray)

public def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name)
    (fixedParamPerms : FixedParamPerms) (fixpointType : Array PartialFixpointType): MetaM Unit := do
  preDefs.forM fun preDef => ensureEqnReservedNamesAvailable preDef.declName
  unless preDefs.all fun p => p.kind.isTheorem do
    unless (← preDefs.allM fun p => isProp p.type) do
      let declNames := preDefs.map (·.declName)
      modifyEnv fun env =>
        preDefs.foldl (init := env) fun env preDef =>
          eqnInfoExt.insert env preDef.declName { preDef with
            declNames, declNameNonRec, fixedParamPerms, fixpointType }

private def deltaLHSUntilFix (declName declNameNonRec : Name) (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | throwTacticEx `deltaLHSUntilFix mvarId "equality expected"
  let lhs' ← deltaExpand lhs fun n => n == declName || n == declNameNonRec
  mvarId.replaceTargetDefEq (← mkEq lhs' rhs)

partial def rwFixUnder (lhs : Expr) : MetaM Expr := do
  if lhs.isAppOfArity ``Order.fix 4 then
    return mkAppN (mkConst ``Order.fix_eq lhs.getAppFn.constLevels!) lhs.getAppArgs
  else if lhs.isAppOfArity ``Order.lfp_monotone 4 then
    return mkAppN (mkConst ``Order.lfp_monotone_fix lhs.getAppFn.constLevels!) lhs.getAppArgs
  else if lhs.isApp then
    let h ← rwFixUnder lhs.appFn!
    mkAppM ``congrFun #[h, lhs.appArg!]
  else if lhs.isProj then
    let f := mkLambda `p .default (← inferType lhs.projExpr!) (lhs.updateProj! (.bvar 0))
    let h ← rwFixUnder lhs.projExpr!
    mkAppM ``congrArg #[f, h]
  else
    throwError "rwFixUnder: unexpected expression {lhs}"

def rwFixEq (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let mut mvarId := mvarId
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | unreachable!
  let h ← rwFixUnder lhs
  let some (_, _, lhsNew) := (← inferType h).eq? | unreachable!
  let targetNew ← mkEq lhsNew rhs
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
  mvarId.assign (← mkEqTrans h mvarNew)
  return mvarNew.mvarId!

/-- Generate the "unfold" lemma for `declName`. -/
def mkUnfoldEq (declName : Name) (info : EqnInfo) : MetaM Name := do
  let name := mkEqLikeNameFor (← getEnv) declName unfoldThmSuffix
  realizeConst declName name (doRealize name)
  return name
where
  doRealize name := withOptions (tactic.hygienic.set · false) do
    lambdaTelescope info.value fun xs body => do
      let us := info.levelParams.map mkLevelParam
      let type ← mkEq (mkAppN (Lean.mkConst declName us) xs) body
      let goal ← withNewMCtxDepth do
        try
          let goal ← mkFreshExprSyntheticOpaqueMVar type
          let mvarId := goal.mvarId!
          trace[Elab.definition.partialFixpoint] "mkUnfoldEq start:{mvarId}"
          let mvarId ← deltaLHSUntilFix declName info.declNameNonRec mvarId
          trace[Elab.definition.partialFixpoint] "mkUnfoldEq after deltaLHS:{mvarId}"
          let mvarId ← rwFixEq mvarId
          trace[Elab.definition.partialFixpoint] "mkUnfoldEq after rwFixEq:{mvarId}"
          withAtLeastTransparency .all <|
            withOptions (smartUnfolding.set · false) <|
              mvarId.refl
          trace[Elab.definition.partialFixpoint] "mkUnfoldEq rfl succeeded"
          instantiateMVars goal
        catch e =>
          throwError "failed to generate unfold theorem for `{.ofConstName declName}`:\n{e.toMessageData}"
      let type ← mkForallFVars xs type
      let type ← letToHave type
      let value ← mkLambdaFVars xs goal

      addDecl <| (←mkThmOrUnsafeDef {
        name := name
        levelParams := info.levelParams
        type := type
        value := value
      })

def getUnfoldFor? (declName : Name) : MetaM (Option Name) := do
  let name := mkEqLikeNameFor (← getEnv) declName unfoldThmSuffix
  let env ← getEnv
  if env.contains name then return name
  let some info := eqnInfoExt.find? env declName | return none
  return some (← mkUnfoldEq declName info)

builtin_initialize
  registerGetUnfoldEqnFn getUnfoldFor?

end Lean.Elab.PartialFixpoint
