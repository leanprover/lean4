/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
module

prelude
public import Lean.Util.HasConstCache
public import Lean.Meta.IndPredBelow
public import Lean.Elab.PreDefinition.Basic
public import Lean.Elab.PreDefinition.Structural.Basic
public import Lean.Elab.PreDefinition.Structural.RecArgInfo

public section

namespace Lean.Elab.Structural
open Meta

private def replaceIndPredRecApp (fixedParamPerm : FixedParamPerm) (funType : Expr) (_i : Nat) (e : Expr) : M Expr := do
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
      let t := t.headBeta
      unless t.getAppFn == funType do return false
      withTraceNodeBefore `Elab.definition.structural (do pure m!"trying {mkFVar localDecl.fvarId} : {localDecl.type}") do
        if ys.size < t.getAppNumArgs then
          trace[Elab.definition.structural] "too few arguments, expected {t.getAppNumArgs}, found {ys.size}. Underapplied recursive call?"
          return false
        if (← (t.getAppArgs.zip ys).allM (fun (t,s) => isDefEq t s)) then
          main.mvarId!.assign (mkAppN (mkAppN localDecl.toExpr mvars) ys[t.getAppNumArgs...*])
          return ← mvars.allM fun v => do
            unless (← v.mvarId!.isAssigned) do
              trace[Elab.definition.structural] "Cannot use {mkFVar localDecl.fvarId}: parameter {v} remains unassigned"
              return false
            return true
        trace[Elab.definition.structural] "Arguments do not match"
        return false
    unless r do
      throwError "Could not eliminate recursive call {e} at {main.mvarId!}"
    instantiateMVars main

private partial def replaceIndPredRecApps (recArgInfos : Array RecArgInfo) (positions : Positions)
    (funTypes : Array Expr) (params : Array Expr) (e : Expr) : M Expr := do
  let recFnNames := recArgInfos.map (·.fnName)
  let containsRecFn (e : Expr) : StateRefT (HasConstCache recFnNames) M Bool :=
    modifyGet (·.contains e)
  let inv := positions.inverse
  let rec loop (e : Expr) : StateRefT (HasConstCache recFnNames) M Expr := do
    unless ← containsRecFn e do
      return e
    match e with
    | .lam n d b c =>
      withLocalDecl n c (← loop d) fun x => do
        mkLambdaFVars #[x] (← loop (b.instantiate1 x))
    | .forallE n d b c =>
      withLocalDecl n c (← loop d) fun x => do
        mkForallFVars #[x] (← loop (b.instantiate1 x))
    | .letE n type val body nondep =>
      mapLetDecl n (← loop type) (← loop val) (nondep := nondep) fun x => do
        loop (body.instantiate1 x)
    | .mdata _ b => do
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop b
      else
        return e.updateMData! (← loop b)
    | .proj _ _ e' => return e.updateProj! (← loop e')
    | .app _ _ =>
      let processApp (e : Expr) : StateRefT (HasConstCache recFnNames) M Expr := do
        e.withApp fun f args => do
          let args ← args.mapM loop
          if let .const c _ := f then
            if let some fidx := recFnNames.idxOf? c then
              let info := recArgInfos[fidx]!
              let (ind, i) := inv[fidx]!
              return ← replaceIndPredRecApp info.fixedParamPerm funTypes[ind]! i (mkAppN f args)
          return mkAppN (← loop f) args
      let some matcherApp ← matchMatcherApp? e | processApp e
      if recArgInfos.all (fun i => !recArgHasLooseBVarsAt i.fnName i.recArgPos e) then
        return ← processApp e
      trace[Elab.definition.structural] "matcherApp before adding below transformation:\n{matcherApp.toExpr}"
      if let some (newApp, addMatcher) ← IndPredBelow.mkBelowMatcher matcherApp params then
        modifyThe State fun s => { s with addMatchers := s.addMatchers.push addMatcher }
        let some _newApp ← matchMatcherApp? newApp | throwError "not a matcherApp: {newApp}"
        trace[Elab.definition.structural] "modified matcher:\n{newApp}"
        processApp newApp
      else
        -- Note: `recArgHasLooseBVarsAt` has false positives, so sometimes everything might stay
        -- the same
        processApp e
    | _ =>
      ensureNoRecFn recFnNames e
      pure e
  loop e |>.run' {}

/-
def withFunTypes (motives : Array Expr) (k : Array Expr → M α) : M α :=
  go 0 #[]
where
  go (i : Nat) (vars : Array Expr) : M α := do
    if h : i < motives.size then
      let funType := motives[i]
      withLetDecl ((`funType).appendIndexAfter (i + 1)) (← inferType funType) funType fun funType => do
        go (i + 1) (vars.push funType)
    else
      k vars
  termination_by motives.size - i
-/

/--
Turns `fun a b => x` into `let funType := fun a b => α` (where `x : α`).
The continuation is the called with all `funType`s corresponding to the values.
-/
def withFunTypes (values : Array Expr) (k : Array Expr → M α) : M α := do
  go 0 #[]
where
  go (i : Nat) (res : Array Expr) : M α :=
    if h : i < values.size then
      lambdaTelescope values[i] fun xs value => do
        let type := (← inferType value).headBeta
        let funType ← mkLambdaFVars xs type
        withLetDecl ((`funType).appendIndexAfter (i + 1)) (← inferType funType) funType
          fun funType => go (i + 1) (res.push funType)
    else
      k res
  termination_by values.size - i

/--
Calculates the `.brecOn` motive corresponding to one structural recursive function.
The `value` is the function with (only) the fixed parameters moved into the context.
-/
def mkIndPredBRecOnMotive (recArgInfo : RecArgInfo) (value funType : Expr) : M Expr := do
  lambdaTelescope value fun xs _ => do
    let type := mkAppN funType xs
    let (indexMajorArgs, otherArgs) := recArgInfo.pickIndicesMajor xs
    let motive ← mkForallFVars otherArgs type
    mkLambdaFVars indexMajorArgs motive

/--
Calculates the `.brecOn` functional argument corresponding to one structural recursive function.
The `value` is the function with (only) the fixed parameters moved into the context,
The `FType` is the expected type of the argument.
The `recArgInfos` is used to transform the body of the function to replace recursive calls with
uses of the `below` induction hypothesis.
-/
def mkIndPredBRecOnF (recArgInfos : Array RecArgInfo) (positions : Positions)
    (recArgInfo : RecArgInfo) (value : Expr) (FType : Expr) (funTypes params : Array Expr) : M Expr := do
  lambdaTelescope value fun xs value => do
    let (indicesMajorArgs, otherArgs) := recArgInfo.pickIndicesMajor xs
    let FType ← instantiateForall FType indicesMajorArgs
    forallBoundedTelescope FType (some 1) fun below _ => do
      let below := below[0]!
      let valueNew ← replaceIndPredRecApps recArgInfos positions funTypes params value
      mkLambdaFVars (indicesMajorArgs ++ #[below] ++ otherArgs) valueNew
/-
/--
Transform the body of a recursive function into a non-recursive one.

The `value` is the function with (only) the fixed parameters instantiated.
-/
def mkIndPredBRecOn (recArgInfos : Array RecArgInfo) (value : Array Expr) : M Expr := do
  let indInfo := recArgInfos[0]!.indGroupInst
  let pos : Positions := .groupAndSort (·.indIdx) recArgInfos (Array.range indInfo.numTypeFormers)
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
        let valueNew     ← replaceIndPredRecApps recArgInfo funType
          (recArgInfo.indGroupInst.params.push motive) value
        let Farg         ← mkLambdaFVars (indexMajorArgs ++ #[below] ++ otherArgs) valueNew
        let brecOn       := mkApp brecOn Farg
        let brecOn       := mkAppN brecOn otherArgs
        let brecOn       ← mkLetFVars #[funType] brecOn
        mkLambdaFVars ys brecOn
-/
end Lean.Elab.Structural
