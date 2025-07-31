/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
public import Lean.Elab.PreDefinition.Basic
public import Lean.Elab.PreDefinition.Eqns
public import Lean.Meta.Tactic.Apply
public import Lean.Elab.Tactic.Simp

public section

namespace Lean.Elab.WF
open Meta
open Eqns

private def rwFixEq (mvarId : MVarId) : MetaM MVarId := mvarId.withContext do
  let target ← mvarId.getType'
  let some (_, lhs, rhs) := target.eq? | unreachable!

  -- lhs should be an application of the declNameNonrec, which unfolds to an
  -- application of fix in one step
  let some lhs' ← delta? lhs | throwError "rwFixEq: cannot delta-reduce {lhs}"
  let_expr WellFounded.fix _α _C _r _hwf F x := lhs'
    | throwTacticEx `rwFixEq mvarId "expected saturated fixed-point application in {lhs'}"
  let h := mkAppN (mkConst ``WellFounded.fix_eq lhs'.getAppFn.constLevels!) lhs'.getAppArgs

  -- We used to just rewrite with `fix_eq` and continue with whatever RHS that produces, but that
  -- would include more copies of `fix` resulting in large and confusing terms.
  -- Instead we manually construct the new term in terms of the current functions,
  -- which should be headed by the `declNameNonRec`, and should be defeq to the expected type

  -- if lhs == e x and lhs' == fix .., then lhsNew := e x = F x (fun y _ => e y)
  let ftype := (← inferType (mkApp F x)).bindingDomain!
  let f' ← forallBoundedTelescope ftype (some 2) fun ys _ => do
    mkLambdaFVars ys (.app lhs.appFn! ys[0]!)
  let lhsNew := mkApp2 F x f'
  let targetNew ← mkEq lhsNew rhs
  let mvarNew ← mkFreshExprSyntheticOpaqueMVar targetNew
  mvarId.assign (← mkEqTrans h mvarNew)
  return mvarNew.mvarId!

def isForallMotive (matcherApp : MatcherApp) : MetaM (Option Expr) := do
  lambdaBoundedTelescope matcherApp.motive matcherApp.discrs.size fun xs t =>
    if xs.size == matcherApp.discrs.size && t.isForall && !t.bindingBody!.hasLooseBVar 0 then
      return some (← mkLambdaFVars xs t.bindingBody!)
    else
      return none

builtin_simproc matcherPushArg (_) := fun e => do
  let e := e.headBeta
  let some matcherApp ← matchMatcherApp? e (alsoCasesOn := true) | return .continue
  trace[Elab.definition.wf.eqns] "matcherUnAddArg: {e}"
  -- The first remaining argument is of the form `(fun x p => f x) arg
  let some fArg := matcherApp.remaining[0]? | return .continue
  unless fArg.isLambda do return .continue
  unless fArg.bindingBody!.isLambda do return .continue
  unless fArg.bindingBody!.bindingBody!.isApp do return .continue
  if fArg.bindingBody!.bindingBody!.hasLooseBVar 0 then return .continue
  unless fArg.bindingBody!.bindingBody!.appArg! == .bvar 1 do return .continue
  if fArg.bindingBody!.bindingBody!.appFn!.hasLooseBVar 1 then return .continue
  let fExpr := fArg.bindingBody!.bindingBody!.appFn!

  -- Check that the motive has an extra parameter (from MatcherApp.addArg)
  let some motive' ← isForallMotive matcherApp |  return .continue
  -- Check that it is ignored by all alternatives
  let mut alts' := #[]
  for altNumParams in matcherApp.altNumParams, alt in matcherApp.alts do
    let some alt' ← lambdaBoundedTelescope alt altNumParams fun xs body => do
      unless xs.size == altNumParams do return none
      unless body.isLambda do return none
      -- Not fully type correct, as the ignored argument has a wrong type
      -- Let's see if it works, or if we need to figure out the right type here
      let f' ← forallBoundedTelescope body.bindingDomain! (some 2) fun xs _ =>
        mkLambdaFVars xs (.app fExpr xs[0]!)
      let alt' ← mkLambdaFVars xs (body.bindingBody!.instantiate1 f')
      return some alt'
      | return .continue
    alts' := alts'.push alt'
  trace[Elab.definition.wf.eqns] "pushing in {fExpr}"
  let remaining' := matcherApp.remaining[1...*]
  let matcherApp' := { matcherApp with motive := motive', alts := alts', remaining := remaining' }
  let e' := matcherApp'.toExpr
  let proof ← mkSorry (← mkEq e e') true
  return .continue (some { expr := matcherApp'.toExpr, proof? := some proof })

private def mkUnfoldProof' (declName : Name) (mvarId : MVarId) : MetaM Unit := withReducible do
  trace[Elab.definition.wf.eqns] "mkUnfoldProf': {MessageData.ofGoal mvarId}"
  let ctx ← Simp.mkContext (config := { dsimp := false, etaStruct := .none, letToHave := false, singlePass := true })
  let simprocs ← ({} : Simp.SimprocsArray).add ``matcherPushArg (post := false)
  match (← simpTarget mvarId ctx (simprocs := simprocs)).1 with
  | none => return ()
  | some mvarId' =>
    try mvarId'.refl
    catch  _ =>
      throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId'}"


private partial def mkUnfoldProof (declName : Name) (mvarId : MVarId) : MetaM Unit := do
  trace[Elab.definition.wf.eqns] "step\n{MessageData.ofGoal mvarId}"
  if ← withAtLeastTransparency .all (tryURefl mvarId) then
    trace[Elab.definition.wf.eqns] "refl!"
    return ()
  else if (← tryContradiction mvarId) then
    trace[Elab.definition.wf.eqns] "contradiction!"
    return ()
  else if let some mvarId ← simpMatch? mvarId then
    trace[Elab.definition.wf.eqns] "simpMatch!"
    mkUnfoldProof declName mvarId
  else if let some mvarId ← simpIf? mvarId (useNewSemantics := true) then
    trace[Elab.definition.wf.eqns] "simpIf!"
    mkUnfoldProof declName mvarId
  else
    let ctx ← Simp.mkContext (config := { dsimp := false, etaStruct := .none })
    match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
    | TacticResultCNM.closed => return ()
    | TacticResultCNM.modified mvarId =>
      trace[Elab.definition.wf.eqns] "simp only!"
      mkUnfoldProof declName mvarId
    | TacticResultCNM.noChange =>
      if let some mvarIds ← casesOnStuckLHS? mvarId then
        trace[Elab.definition.wf.eqns] "case split into {mvarIds.size} goals"
        mvarIds.forM (mkUnfoldProof declName)
      else if let some mvarIds ← splitTarget? mvarId (useNewSemantics := true) then
        trace[Elab.definition.wf.eqns] "splitTarget into {mvarIds.length} goals"
        mvarIds.forM (mkUnfoldProof declName)
      else
        -- At some point in the past, we looked for occurrences of Wf.fix to fold on the
        -- LHS (introduced in 096e4eb), but it seems that code path was never used,
        -- so #3133 removed it again (and can be recovered from there if this was premature).
        throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"

def mkUnfoldEq (preDef : PreDefinition) (unaryPreDefName : Name) (wfPreprocessProof : Simp.Result) : MetaM Unit := do
  let name := mkEqLikeNameFor (← getEnv) preDef.declName unfoldThmSuffix
  prependError m!"Cannot derive {name}" do
  withOptions (tactic.hygienic.set · false) do
    lambdaTelescope preDef.value fun xs body => do
      let us := preDef.levelParams.map mkLevelParam
      let lhs := mkAppN (Lean.mkConst preDef.declName us) xs
      let type ← mkEq lhs body

      let main ← mkFreshExprSyntheticOpaqueMVar type
      let mvarId := main.mvarId!
      let wfPreprocessProof ← Simp.mkCongr { expr := type.appFn! } (← wfPreprocessProof.addExtraArgs xs)
      let mvarId ← applySimpResultToTarget mvarId type wfPreprocessProof
      let mvarId ← if preDef.declName != unaryPreDefName then deltaLHS mvarId else pure mvarId
      let mvarId ← rwFixEq mvarId
      mkUnfoldProof' preDef.declName mvarId

      let value ← instantiateMVars main
      let type ← mkForallFVars xs type
      let type ← letToHave type
      let value ← mkLambdaFVars xs value
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := preDef.levelParams
      }
      inferDefEqAttr name
      trace[Elab.definition.wf] "mkUnfoldEq defined {.ofConstName name}"

/--
Derives the equational theorem for the individual functions from the equational
theorem of `foo._unary` or `foo._binary`.

It should just be a specialization of that one, due to defeq.
-/
def mkBinaryUnfoldEq (preDef : PreDefinition) (unaryPreDefName : Name) : MetaM Unit := do
  let name := mkEqLikeNameFor (← getEnv) preDef.declName unfoldThmSuffix
  let unaryEqName:= mkEqLikeNameFor (← getEnv) unaryPreDefName unfoldThmSuffix
  prependError m!"Cannot derive {name} from {unaryEqName}" do
  withOptions (tactic.hygienic.set · false) do
    lambdaTelescope preDef.value fun xs body => do
      let us := preDef.levelParams.map mkLevelParam
      let lhs := mkAppN (Lean.mkConst preDef.declName us) xs
      let type ← mkEq lhs body
      let main ← mkFreshExprSyntheticOpaqueMVar type
      let mvarId := main.mvarId!
      let mvarId ← deltaLHS mvarId -- unfold the function
      let mvarIds ← mvarId.applyConst unaryEqName
      unless mvarIds.isEmpty do
        throwError "Failed to apply '{unaryEqName}' to '{mvarId}'"

      let value ← instantiateMVars main
      let type ← mkForallFVars xs type
      let type ← letToHave type
      let value ← mkLambdaFVars xs value
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := preDef.levelParams
      }
      inferDefEqAttr name
      trace[Elab.definition.wf] "mkBinaryUnfoldEq defined {.ofConstName name}"

builtin_initialize
  registerTraceClass `Elab.definition.wf.eqns

end Lean.Elab.WF
