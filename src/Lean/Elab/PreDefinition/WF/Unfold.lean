/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Eqns

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
  else if let some mvarId ← simpIf? mvarId then
    trace[Elab.definition.wf.eqns] "simpIf!"
    mkUnfoldProof declName mvarId
  else if let some mvarId ← whnfReducibleLHS? mvarId then
    trace[Elab.definition.wf.eqns] "whnfReducibleLHS!"
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
      else if let some mvarIds ← splitTarget? mvarId then
        trace[Elab.definition.wf.eqns] "splitTarget into {mvarIds.length} goals"
        mvarIds.forM (mkUnfoldProof declName)
      else
        -- At some point in the past, we looked for occurrences of Wf.fix to fold on the
        -- LHS (introduced in 096e4eb), but it seems that code path was never used,
        -- so #3133 removed it again (and can be recovered from there if this was premature).
        throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"

def mkUnfoldEq (preDef : PreDefinition) (unaryPreDefName : Name) (wfPreprocessProof : Simp.Result) : MetaM Unit := do
  let baseName := preDef.declName
  let name := Name.str baseName unfoldThmSuffix
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
      mkUnfoldProof preDef.declName mvarId

      let value ← instantiateMVars main
      let type ← mkForallFVars xs type
      let value ← mkLambdaFVars xs value
      addDecl <| Declaration.thmDecl {
        name, type, value
        levelParams := preDef.levelParams
      }
      trace[Elab.definition.wf] "mkUnfoldEq defined {.ofConstName name}"

builtin_initialize
  registerTraceClass `Elab.definition.wf.eqns

end Lean.Elab.WF
