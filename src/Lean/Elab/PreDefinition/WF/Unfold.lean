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

-- builtin_dsimproc removeMData (_) := fun e => do
--   return if e.isMData then .continue e.consumeMData else .continue

/--
Generates a theorem of the form
```
matcherArgPusher params motive {α} {β} (f : ∀ (x : α), β x) rel alt1 .. x1 x2
  :
  matcher params (motive := fun x1 x2 => ((y : α) → rel x1 x2 y → β y) → motive x1 x2)
    (alt1 := fun z1 z2 z2 f => alt1 z1 z2 z2 f) …
    x1 x2
    (fun y _h => f y)
  =
  matcher params (motive := motive)
    (alt1 := fun z1 z2 z2 => alt1 z1 z2 z2 (fun y _ => f y)) …
    x1 x2
```
-/
def mkMatchArgPusher (matcherName : Name) (matcherInfo : MatcherInfo) : MetaM Name := do
  let matcherVal ← getConstVal matcherName
  forallBoundedTelescope matcherVal.type (some (matcherInfo.numParams + 1)) fun xs _ => do
    let params := xs[*...matcherInfo.numParams]
    let motive := xs[matcherInfo.numParams]!
    -- TODO: Levels
    withLocalDeclD `α (.sort 1) fun alpha => do
    withLocalDeclD `β (← mkArrow alpha (.sort 1)) fun beta => do
    withLocalDeclD `f (.forallE `x alpha (mkApp beta (.bvar 0)) .default) fun f => do
    let relType ← forallTelescope (← inferType motive) fun xs _ =>
      mkForallFVars xs (.forallE `x alpha (.sort 0) .default)
    withLocalDeclD `rel relType fun rel => do
    let motive' ← forallTelescope (← inferType motive) fun xs _ => do
      let motiveBody := mkAppN motive xs
      let extraArgType := .forallE `y alpha (.forallE `h (mkAppN rel (xs.push (.bvar 0))) (mkApp beta (.bvar 1)) .default) .default
      let motiveBody ← mkArrow extraArgType motiveBody
      mkLambdaFVars xs motiveBody
    let us := matcherVal.levelParams.map mkLevelParam -- TODO
    let lhs := mkAppN (.const matcherName us) params
    let rhs := mkAppN (.const matcherName us) params
    let lhs := mkApp lhs motive'
    let rhs := mkApp rhs motive
    forallBoundedTelescope (← inferType lhs) matcherInfo.numDiscrs fun discrs _ => do
    let lhs := mkAppN lhs discrs
    let rhs := mkAppN rhs discrs
    forallBoundedTelescope (← inferType lhs) matcherInfo.numAlts fun alts _ => do
    let lhs := mkAppN lhs alts

    let mut rhs := rhs
    for alt in alts, altNumParams in matcherInfo.altNumParams do
      let alt' ← forallBoundedTelescope (← inferType alt) altNumParams fun ys altBodyType => do
        assert! altBodyType.isForall
        let altArg ← forallBoundedTelescope altBodyType.bindingDomain! (some 2) fun ys _ => do
          mkLambdaFVars ys (.app f ys[0]!)
        mkLambdaFVars ys (mkAppN alt (ys.push altArg))
      rhs := mkApp rhs alt'

    let extraArg := .lam `y alpha (.lam `h (mkAppN rel (discrs.push (.bvar 0))) (mkApp f (.bvar 1)) .default) .default
    let lhs := mkApp lhs extraArg
    let goal ← mkEq lhs rhs
    let name := .str matcherName "_arg_pusher"

    let type := goal
    let type ← mkForallFVars (params ++ #[motive, alpha, beta, f, rel] ++ discrs ++ alts) type
    addDecl <| Declaration.axiomDecl { name := name, levelParams := matcherVal.levelParams, type := type, isUnsafe := false }
    return name

builtin_simproc_decl matcherPushArg (_) := fun e => do
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
  let beta ← forallBoundedTelescope (← inferType fExpr) (some 1) fun xs body =>
    mkLambdaFVars xs body
  let alpha := beta.bindingDomain!

  -- Check that the motive has an extra parameter (from MatcherApp.addArg)
  let some motive' ← isForallMotive matcherApp |  return .continue
  let rel ← lambdaTelescope matcherApp.motive fun xs motiveBody =>
    let motiveBodyArg := motiveBody.bindingDomain!
    mkLambdaFVars xs (.lam motiveBodyArg.bindingName! motiveBodyArg.bindingDomain! motiveBodyArg.bindingBody!.bindingDomain! .default)

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

  -- TODO: de-duplicate with addArg
  let matcherLevels' ← match matcherApp.uElimPos? with
    | none     => pure matcherApp.matcherLevels
    | some pos =>
      let uElim ← lambdaTelescope motive' fun _xs motiveBody =>
        getLevel motiveBody
      pure <| matcherApp.matcherLevels.set! pos uElim

  let matcherApp' := { matcherApp with
    matcherLevels := matcherLevels'
    motive := motive'
    alts := alts'
    remaining := remaining' }
  -- let e' := matcherApp'.toExpr
  let proof ← -- .app (mkConst `justATest) (← mkEq e e')
    mkAppOptM (← mkMatchArgPusher matcherApp.matcherName matcherApp.toMatcherInfo)
      ((matcherApp.params ++ #[motive', alpha, beta, fExpr, rel] ++ matcherApp.discrs ++ matcherApp.alts).map some)
  return .continue (some { expr := matcherApp'.toExpr, proof? := some proof })


private def mkUnfoldProof' (declName : Name) (mvarId : MVarId) : MetaM Unit := withReducible do
  trace[Elab.definition.wf.eqns] "mkUnfoldProf': {MessageData.ofGoal mvarId}"
  let ctx ← Simp.mkContext (config := { dsimp := false, etaStruct := .none, letToHave := false, singlePass := true })
  let simprocs := ({} : Simp.SimprocsArray)
  let simprocs ← simprocs.add ``matcherPushArg (post := false)
  -- let simprocs ← simprocs.add ``removeMData (post := false)
  match (← simpTarget mvarId ctx (simprocs := simprocs)).1 with
  | none => return ()
  | some mvarId' =>
    prependError m!"failed to generate equational theorem for '{declName}'" do
      mvarId'.refl


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
