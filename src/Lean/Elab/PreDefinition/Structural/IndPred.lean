/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dany Fabian
-/
module

prelude
public import Lean.Elab.PreDefinition.Structural.Basic
public import Lean.Elab.PreDefinition.Structural.RecArgInfo
import Lean.Util.HasConstCache
import Lean.Meta.IndPredBelow
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Omega

namespace Lean.Elab.Structural
open Meta

open IndPredBelow (RecursionContext)

/-- Return the `i`th projection of the type `e` where `e` has `n` Ands. -/
def andProj (i n : Nat) (e : Expr) : Expr :=
  match i, n with
  | 0, 1 => e
  | 0, _ + 1 => .proj ``And 0 e
  | i + 1, k + 1 => andProj i k (.proj ``And 1 e)
  | _, _ => e

def replaceIndPredRecApp (recArgInfo : RecArgInfo) (ctx : RecursionContext) (fidx : Nat)
    (positions : Positions) (e : Expr) (args : Array Expr) : MetaM Expr := do
  let some recArg := args[recArgInfo.recArgPos]? |
    throwError "insufficient number of parameters at recursive application {indentExpr e}"
  let recArg ← whnfCore recArg
  let fail {α} : MetaM α := do throwError "failed to eliminate recursive application{indentExpr e}"
  let .fvar recVar := recArg.getAppFn | fail
  let some (motiveIdx, e) := ctx.motives.get? recVar | fail
  let recApp := mkAppN e recArg.getAppArgs
  let some pos := positions[motiveIdx]!.idxOf? fidx | fail
  let mut ys := #[]
  for h : i in *...args.size do
    unless recArgInfo.indicesPos.contains i || i == recArgInfo.recArgPos do
      unless recArgInfo.fixedParamPerm.isFixed i do
        ys := ys.push args[i]
  let recApp := andProj pos positions[motiveIdx]!.size recApp
  return mkAppN recApp ys

partial def replaceIndPredRecApps (recArgInfos : Array RecArgInfo) (positions : Positions)
    (params : Array Expr) (ctx : RecursionContext) (e : Expr) : M Expr := do
  let recFnNames := recArgInfos.map (·.fnName)
  let containsRecFn (e : Expr) : StateRefT (HasConstCache recFnNames) M Bool :=
    modifyGet (·.contains e)
  let rec loop (ctx : RecursionContext) (e : Expr) : StateRefT (HasConstCache recFnNames) M Expr := do
    unless ← containsRecFn e do
      return e
    match e with
    | .lam n d b c =>
      withLocalDecl n c (← loop ctx d) fun x => do
        mkLambdaFVars #[x] (← loop ctx (b.instantiate1 x))
    | .forallE n d b c =>
      withLocalDecl n c (← loop ctx d) fun x => do
        mkForallFVars #[x] (← loop ctx (b.instantiate1 x))
    | .letE n type val body nondep =>
      mapLetDecl n (← loop ctx type) (← loop ctx val) (nondep := nondep) fun x => do
        loop ctx (body.instantiate1 x)
    | .mdata _ b => do
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop ctx b
      else
        return e.updateMData! (← loop ctx b)
    | .proj _ _ e' => return e.updateProj! (← loop ctx e')
    | .app _ _ =>
      let processApp (e : Expr) : StateRefT (HasConstCache recFnNames) M Expr := do
        e.withApp fun f args => do
          let args ← args.mapM (loop ctx)
          if let .const c _ := f then
            if let some fidx := recFnNames.idxOf? c then
              return ← replaceIndPredRecApp recArgInfos[fidx]! ctx fidx positions e args
          return mkAppN (← loop ctx f) args
      let some matcherApp ← matchMatcherApp? e | processApp e
      if recArgInfos.all (fun i => !recArgHasLooseBVarsAt i.fnName i.recArgPos e) then
        return ← processApp e
      trace[Elab.definition.structural] "matcherApp before adding below transformation:\n{matcherApp.toExpr}"
      let nrealParams := recArgInfos[0]!.indGroupInst.params.size
      let matcherResult ← controlAt MetaM fun g =>
        IndPredBelow.mkBelowMatcher matcherApp params nrealParams ctx fun ctx e =>
          g (loop ctx e)
      if let some (newApp, addMatcher) := matcherResult then
        modifyThe State fun s => { s with addMatchers := s.addMatchers.push addMatcher }
        processApp newApp -- recursive applications may still be hidden in e.g. the discriminants
      else
        -- Note: `recArgHasLooseBVarsAt` has false positives, so sometimes everything might stay
        -- the same
        processApp e
    | _ =>
      ensureNoRecFn recFnNames e
      pure e
  loop ctx e |>.run' {}

/--
Turns `fun a b => x` into `let funType := fun a b => α` (where `x : α`).
The continuation is the called with all `funType`s corresponding to the values.
-/
public def withFunTypes (values : Array Expr) (k : Array Expr → M α) : M α := do
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
public def mkIndPredBRecOnMotive (recArgInfo : RecArgInfo) (value funType : Expr) : M Expr := do
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
public def mkIndPredBRecOnF (recArgInfos : Array RecArgInfo) (positions : Positions)
    (recArgInfo : RecArgInfo) (value : Expr) (FType : Expr) (params : Array Expr) : M Expr := do
  lambdaTelescope value fun xs value => do
    let (indicesMajorArgs, otherArgs) := recArgInfo.pickIndicesMajor xs
    let FType ← instantiateForall FType indicesMajorArgs
    forallBoundedTelescope FType (some 1) fun below _ => do
      let below := below[0]!
      let belowName := (← inferType below).getForallBody.getAppFn.constName!
      let ctx := {
        belows := .insert {} indicesMajorArgs.back!.fvarId! (belowName, below)
        motives := {}
      }
      let valueNew ← withDeclNameForAuxNaming recArgInfo.fnName <|
        replaceIndPredRecApps recArgInfos positions params ctx value
      mkLambdaFVars (indicesMajorArgs ++ #[below] ++ otherArgs) valueNew

end Lean.Elab.Structural
