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

/--
Given `t = a ∧ b ∧ c ∧ ...`, return the `i`th type (of `n` total) or `none` if `n ≤ i` or there
aren't enough `And`s to get the `i`th one.
-/
def andProjType (i n : Nat) (t : Expr) : Option Expr :=
  match i, n, t with
  | 0, 1, t => some t
  | 0, _ + 1, mkApp2 (.const ``And _) a _ => some a
  | i + 1, k + 1, mkApp2 (.const ``And _) _ b => andProjType i k b
  | _, _, _ => none

/-- Return the `i`th projection of the type `e` where `e` has `n` Ands. -/
def andProj (i n : Nat) (e : Expr) : Expr :=
  match i, n with
  | 0, 1 => e
  | 0, _ + 1 => .proj ``And 0 e
  | i + 1, k + 1 => andProj i k (.proj ``And 1 e)
  | _, _ => e

private def replaceIndPredRecApp (fixedParamPerm : FixedParamPerm) (funType : Expr) (i n : Nat) (e : Expr) : M Expr := do
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
      let some t := andProjType i n t | return false
      unless t.getAppFn == funType do return false
      withTraceNodeBefore `Elab.definition.structural (do pure m!"trying {mkFVar localDecl.fvarId} : {localDecl.type}") do
        if ys.size < t.getAppNumArgs then
          trace[Elab.definition.structural] "too few arguments, expected {t.getAppNumArgs}, found {ys.size}. Underapplied recursive call?"
          return false
        if (← (t.getAppArgs.zip ys).allM (fun (t,s) => isDefEq t s)) then
          let recApp := mkAppN (mkAppN localDecl.toExpr mvars) ys[t.getAppNumArgs...*]
          let recApp := andProj i n recApp
          main.mvarId!.assign recApp
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
              let j := positions[ind]!.size
              return ← replaceIndPredRecApp info.fixedParamPerm funTypes[fidx]! i j (mkAppN f args)
          return mkAppN (← loop f) args
      let some matcherApp ← matchMatcherApp? e | processApp e
      if recArgInfos.all (fun i => !recArgHasLooseBVarsAt i.fnName i.recArgPos e) then
        return ← processApp e
      trace[Elab.definition.structural] "matcherApp before adding below transformation:\n{matcherApp.toExpr}"
      let nrealParams := recArgInfos[0]!.indGroupInst.params.size
      if let some (newApp, addMatcher) ← IndPredBelow.mkBelowMatcher matcherApp params nrealParams then
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

end Lean.Elab.Structural
