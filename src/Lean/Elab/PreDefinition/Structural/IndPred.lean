/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
prelude
import Lean.Meta.IndPredBelow
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Elab.PreDefinition.Structural.RecArgInfo

namespace Lean.Elab.Structural
open Meta

private def replaceIndPredRecApp (fixedParamPerm : FixedParamPerm) (funType : Expr) (e : Expr) : M Expr := do
  withoutProofIrrelevance do
  withTraceNode `Elab.definition.structural (fun _ => pure m!"eliminating recursive call {e}") do
    -- We want to replace `e` with an expression of the same type
    let main ← mkFreshExprSyntheticOpaqueMVar (← inferType e)
    let args : Array Expr := e.getAppArgs
    let ys := fixedParamPerm.pickVarying args
    let lctx ← getLCtx
    let r ← lctx.anyM fun localDecl => do
      if localDecl.isAuxDecl then return false
      let (mvars, _, t) ← forallMetaTelescope localDecl.type -- NB: do not reduce, we want to see the `funType`
      unless t.getAppFn == funType do return false
      withTraceNodeBefore `Elab.definition.structural (do pure m!"trying {mkFVar localDecl.fvarId} : {localDecl.type}") do
        if ys.size < t.getAppNumArgs then
          trace[Elab.definition.structural] "too few arguments, expected {t.getAppNumArgs}, found {ys.size}. Underapplied recursive call?"
          return false
        if (← (t.getAppArgs.zip ys).allM (fun (t,s) => isDefEq t s)) then
          main.mvarId!.assign (mkAppN (mkAppN localDecl.toExpr mvars) ys[t.getAppNumArgs:])
          return ← mvars.allM fun v => do
            unless (← v.mvarId!.isAssigned) do
              trace[Elab.definition.structural] "Cannot use {mkFVar localDecl.fvarId}: parameter {v} remains unassigned"
              return false
            return true
        trace[Elab.definition.structural] "Arguments do not match"
        return false
    unless r do
      throwError "Could not eliminate recursive call {e}"
    instantiateMVars main

private partial def replaceIndPredRecApps (recArgInfo : RecArgInfo) (funType : Expr) (motive : Expr) (e : Expr) : M Expr := do
  let rec loop (e : Expr) : M Expr := do
    match e with
    | Expr.lam n d b c =>
      withLocalDecl n c (← loop d) fun x => do
        mkLambdaFVars #[x] (← loop (b.instantiate1 x))
    | Expr.forallE n d b c =>
      withLocalDecl n c (← loop d) fun x => do
        mkForallFVars #[x] (← loop (b.instantiate1 x))
    | Expr.letE n type val body _ =>
      withLetDecl n (← loop type) (← loop val) fun x => do
        mkLetFVars #[x] (← loop (body.instantiate1 x))
    | Expr.mdata d b => do
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop b
      else
        return mkMData d (← loop b)
    | Expr.proj n i e    => return mkProj n i (← loop e)
    | Expr.app _ _ =>
      let processApp (e : Expr) : M Expr := do
        e.withApp fun f args => do
          if f.isConstOf recArgInfo.fnName then
            replaceIndPredRecApp recArgInfo.fixedParamPerm funType e
          else
            return mkAppN (← loop f) (← args.mapM loop)
      match (← matchMatcherApp? e) with
      | some matcherApp =>
        if !recArgHasLooseBVarsAt recArgInfo.fnName recArgInfo.recArgPos e then
          processApp e
        else
          trace[Elab.definition.structural] "matcherApp before adding below transformation:\n{matcherApp.toExpr}"
          let rec addBelow (matcherApp : MatcherApp) : M Expr := do
            if let some (t, idx) ← IndPredBelow.findBelowIdx matcherApp.discrs motive then
              let (newApp, addMatcher) ← IndPredBelow.mkBelowMatcher matcherApp motive t idx
              modify fun s => { s with addMatchers := s.addMatchers.push addMatcher }
              let some newApp ← matchMatcherApp? newApp | throwError "not a matcherApp: {newApp}"
              addBelow newApp
            else pure matcherApp.toExpr

          let newApp ← addBelow matcherApp
          if newApp == matcherApp.toExpr then
            throwError "could not add below discriminant"
          else
            trace[Elab.definition.structural] "modified matcher:\n{newApp}"
            processApp newApp
      | none => processApp e
    | e =>
      ensureNoRecFn #[recArgInfo.fnName] e
      pure e
  loop e

/--
Transform the body of a recursive function into a non-recursive one.

The `value` is the function with (only) the fixed parameters instantiated.
-/
def mkIndPredBRecOn (recArgInfo : RecArgInfo) (value : Expr) : M Expr := do
  lambdaTelescope value fun ys value => do
    let type  := (← inferType value).headBeta
    let (indexMajorArgs, otherArgs) := recArgInfo.pickIndicesMajor ys
    trace[Elab.definition.structural] "indexMajorArgs: {indexMajorArgs}, otherArgs: {otherArgs}"
    let funType ← mkLambdaFVars ys type
    withLetDecl `funType (← inferType funType) funType fun funType => do
      let motive ← mkForallFVars otherArgs (mkAppN funType ys)
      let motive ← mkLambdaFVars indexMajorArgs motive
      trace[Elab.definition.structural] "brecOn motive: {motive}"
      let brecOn := Lean.mkConst (mkBRecOnName recArgInfo.indName!) recArgInfo.indGroupInst.levels
      let brecOn := mkAppN brecOn recArgInfo.indGroupInst.params
      let brecOn := mkApp brecOn motive
      let brecOn := mkAppN brecOn indexMajorArgs
      check brecOn
      let brecOnType ← inferType brecOn
      trace[Elab.definition.structural] "brecOn     {brecOn}"
      trace[Elab.definition.structural] "brecOnType {brecOnType}"
      -- we need to close the telescope here, because the local context is used:
      -- The root cause was, that this copied code puts an ih : FType into the
      -- local context and later, when we use the local context to build the recursive
      -- call, it uses this ih. But that ih doesn't exist in the actual brecOn call.
      -- That's why it must go.
      let FType ← forallBoundedTelescope brecOnType (some 1) fun F _ => do
        let F := F[0]!
        let FType ← inferType F
        trace[Elab.definition.structural] "FType: {FType}"
        instantiateForall FType indexMajorArgs
      forallBoundedTelescope FType (some 1) fun below _ => do
        let below := below[0]!
        let valueNew     ← replaceIndPredRecApps recArgInfo funType motive value
        let Farg         ← mkLambdaFVars (indexMajorArgs ++ #[below] ++ otherArgs) valueNew
        let brecOn       := mkApp brecOn Farg
        let brecOn       := mkAppN brecOn otherArgs
        let brecOn       ← mkLetFVars #[funType] brecOn
        mkLambdaFVars ys brecOn

end Lean.Elab.Structural
