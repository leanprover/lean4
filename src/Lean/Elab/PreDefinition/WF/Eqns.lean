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

namespace Lean.Elab.WF
open Meta
open Eqns

structure EqnInfo extends EqnInfoCore where
  declNames       : Array Name
  declNameNonRec  : Name
  fixedPrefixSize : Nat
  argsPacker      : ArgsPacker
  deriving Inhabited

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

private partial def mkProof (declName declNameNonRec : Name) (type : Expr) : MetaM Expr := do
  trace[Elab.definition.wf.eqns] "proving: {type}"
  withNewMCtxDepth do
    let main ← mkFreshExprSyntheticOpaqueMVar type
    let (_, mvarId) ← main.mvarId!.intros
    let rec go (mvarId : MVarId) : MetaM Unit := do
      trace[Elab.definition.wf.eqns] "step\n{MessageData.ofGoal mvarId}"
      if ← withAtLeastTransparency .all (tryURefl mvarId) then
        trace[Elab.definition.wf.eqns] "refl!"
        return ()
      else if (← tryContradiction mvarId) then
        trace[Elab.definition.wf.eqns] "contradiction!"
        return ()
      else if let some mvarId ← simpMatch? mvarId then
        trace[Elab.definition.wf.eqns] "simpMatch!"
        go mvarId
      else if let some mvarId ← simpIf? mvarId then
        trace[Elab.definition.wf.eqns] "simpIf!"
        go mvarId
      else if let some mvarId ← whnfReducibleLHS? mvarId then
        trace[Elab.definition.wf.eqns] "whnfReducibleLHS!"
        go mvarId
      else
        let ctx ← Simp.mkContext (config := { dsimp := false, etaStruct := .none })
        match (← simpTargetStar mvarId ctx (simprocs := {})).1 with
        | TacticResultCNM.closed => return ()
        | TacticResultCNM.modified mvarId =>
          trace[Elab.definition.wf.eqns] "simp only!"
          go mvarId
        | TacticResultCNM.noChange =>
          if let some mvarIds ← casesOnStuckLHS? mvarId then
            trace[Elab.definition.wf.eqns] "case split into {mvarIds.size} goals"
            mvarIds.forM go
          else if let some mvarIds ← splitTarget? mvarId then
            trace[Elab.definition.wf.eqns] "splitTarget into {mvarIds.length} goals"
            mvarIds.forM go
          else
            -- At some point in the past, we looked for occurrences of Wf.fix to fold on the
            -- LHS (introduced in 096e4eb), but it seems that code path was never used,
            -- so #3133 removed it again (and can be recovered from there if this was premature).
            throwError "failed to generate equational theorem for '{declName}'\n{MessageData.ofGoal mvarId}"

    let mvarId ← if declName != declNameNonRec then deltaLHS mvarId else pure mvarId
    let mvarId ← rwFixEq mvarId
    go mvarId
    instantiateMVars main

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
    trace[Elab.definition.wf.eqns] "{eqnTypes[i]}"
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
  registerTraceClass `Elab.definition.wf.eqns

end Lean.Elab.WF
