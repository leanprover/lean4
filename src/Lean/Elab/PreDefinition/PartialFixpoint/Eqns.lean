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
  /-- The fixpoint equation of `declNameNonRec`, see `mkFixEq`. -/
  fixEq?          : Option Name
  deriving Inhabited

public builtin_initialize eqnInfoExt : MapDeclarationExtension EqnInfo ←
  mkMapDeclarationExtension (exportEntriesFn := fun env s =>
    let all := s.toArray
    -- Do not export for non-exposed defs at exported/server levels
    let exported := s.filter (fun n _ => env.hasExposedBody n) |>.toArray
    { exported, server := exported, «private» := all })

/--
Adds `declNameNonRec._functional := fun fixed => F` and
`declNameNonRec._fix_eq : ∀ fixed, declNameNonRec fixed = _functional fixed (declNameNonRec fixed)`,
the fixpoint equation of the packed definition of a mutual block.

The unfold theorem of each function is proved from `_fix_eq` by projection and unfolding
`_functional`. This way the proofs mention neither the monotonicity proof nor the functional of the
whole block, which the kernel would otherwise re-check for each of them. Both are added eagerly,
as realized constants are re-checked by the kernel in every realization that uses them.
-/
private def mkFixEq (declNameNonRec : Name) : MetaM Name := do
  -- `_functional` is exported with its body along with `declNameNonRec`'s, so that `_fix_eq` can
  -- be used for the unfold theorems in importing modules.
  withExporting (isExporting := (← getEnv).hasExposedBody declNameNonRec) do
    let name := mkEqLikeNameFor (← getEnv) declNameNonRec "_fix_eq"
    let functionalName := mkEqLikeNameFor (← getEnv) declNameNonRec "_functional"
    let info ← getConstInfoDefn declNameNonRec
    let us := info.levelParams.map mkLevelParam
    let (functionalType, functionalValue) ← lambdaTelescope info.value fun xs body => do
      unless body.isAppOfArity ``Order.fix 4 || body.isAppOfArity ``Order.lfp_monotone 4 do
        throwError "mkFixEq: unexpected body of `{.ofConstName declNameNonRec}`:{indentExpr body}"
      let F := body.appFn!.appArg!
      return (← mkForallFVars xs (← inferType F), ← mkLambdaFVars xs F)
    addDecl <| .defnDecl {
      name := functionalName, type := functionalType, value := functionalValue
      levelParams := info.levelParams
      hints := .abbrev, safety := .safe }
    modifyEnv (addNoncomputable · functionalName)
    let (type, value) ← lambdaTelescope info.value fun xs body => do
      let lhs := mkAppN (mkConst declNameNonRec us) xs
      let rhs := mkApp (mkAppN (mkConst functionalName us) xs) lhs
      let thm := if body.isAppOf ``Order.fix then ``Order.fix_eq else ``Order.lfp_monotone_fix
      let value := mkAppN (mkConst thm body.getAppFn.constLevels!) body.getAppArgs
      return (← mkForallFVars xs (← mkEq lhs rhs), ← mkLambdaFVars xs value)
    addDecl <| (← mkThmOrUnsafeDef { name, type, value, levelParams := info.levelParams })
    return name

public def registerEqnsInfo (preDefs : Array PreDefinition) (declNameNonRec : Name)
    (fixedParamPerms : FixedParamPerms) (fixpointType : Array PartialFixpointType): MetaM Unit := do
  preDefs.forM fun preDef => ensureEqnReservedNamesAvailable preDef.declName
  unless preDefs.all fun p => p.kind.isTheorem do
    unless (← preDefs.allM fun p => isProp p.type) do
      let declNames := preDefs.map (·.declName)
      let fixEq? ← if declNameNonRec != preDefs[0]!.declName then
        some <$> mkFixEq declNameNonRec
      else
        pure none
      modifyEnv fun env =>
        preDefs.foldl (init := env) fun env preDef =>
          eqnInfoExt.insert env preDef.declName { preDef with
            declNames, declNameNonRec, fixedParamPerms, fixpointType, fixEq? }

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

/--
Rewrites the occurrence of `declNameNonRec fixed` in the left-hand side with `fixEq`, using a single
`congrArg` so that the proof does not contain a copy of the packed functional per projection.
-/
def rwFixEqWith (declNameNonRec fixEq : Name) (numFixed : Nat) (mvarId : MVarId) : MetaM MVarId :=
    mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | unreachable!
  let some packed := lhs.find? (·.isAppOfArity declNameNonRec numFixed) |
    throwTacticEx `rwFixEqWith mvarId m!"no application of `{.ofConstName declNameNonRec}` found"
  let f := mkLambda `p .default (← inferType packed) (← kabstract lhs packed)
  let h := mkAppN (mkConst fixEq packed.getAppFn.constLevels!) packed.getAppArgs
  let h ← mkCongrArg f h
  let some (_, _, lhsNew) := (← inferType h).eq? | unreachable!
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar (← mkEq lhsNew.headBeta rhs)
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
          let mvarId ← if let some fixEq := info.fixEq? then
            let mvarId ← deltaLHSUntilFix declName .anonymous mvarId
            trace[Elab.definition.partialFixpoint] "mkUnfoldEq after deltaLHS:{mvarId}"
            rwFixEqWith info.declNameNonRec fixEq info.fixedParamPerms.numFixed mvarId
          else
            let mvarId ← deltaLHSUntilFix declName info.declNameNonRec mvarId
            trace[Elab.definition.partialFixpoint] "mkUnfoldEq after deltaLHS:{mvarId}"
            rwFixEq mvarId
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
