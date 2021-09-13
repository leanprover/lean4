/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab.Structural
open Meta

partial def addSmartUnfoldingDefAux (preDef : PreDefinition) (matcherBelowDep : NameSet) : MetaM PreDefinition := do
  let recFnName := preDef.declName
  let isMarkedMatcherName (n : Name) : Bool    := matcherBelowDep.contains n
  let isMarkedMatcherConst (e : Expr) : Bool   := e.isConst && isMarkedMatcherName e.constName!
  let isMarkedMatcherApp (e : Expr) : Bool     := isMarkedMatcherConst e.getAppFn
  let containsMarkedMatcher (e : Expr) : Bool := e.find? isMarkedMatcherConst |>.isSome
  let rec visit (e : Expr) : MetaM Expr := do
    match e with
    | Expr.lam ..     => lambdaTelescope e fun xs b => do mkLambdaFVars xs (← visit b)
    | Expr.forallE .. => forallTelescope e fun xs b => do mkForallFVars xs (← visit b)
    | Expr.letE n type val body _ =>
      withLetDecl n type (← visit val) fun x => do
        mkLetFVars #[x] (← visit (body.instantiate1 x))
    | Expr.mdata d b _   => return mkMData d (← visit b)
    | Expr.proj n i s _  => return mkProj n i (← visit s)
    | Expr.app .. =>
      let processApp (e : Expr) : MetaM Expr :=
        e.withApp fun f args => do
          return mkAppN (← visit f) (← args.mapM visit)
      match isMarkedMatcherApp e, (← matchMatcherApp? e) with
      | true, some matcherApp =>
        let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
          lambdaTelescope alt fun xs altBody => do
            unless xs.size >= numParams do
              throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
            if containsMarkedMatcher altBody then
              -- continue
              mkLambdaFVars xs (← visit altBody)
            else
              -- add idRhs marker
              let altBody ← mkLambdaFVars xs[numParams:xs.size] altBody
              let altBody ← mkIdRhs altBody
              mkLambdaFVars xs[0:numParams] altBody
        pure { matcherApp with alts := altsNew }.toExpr
      | _, _ => processApp e
    | _ => pure e
  return { preDef with
    declName  := mkSmartUnfoldingNameFor preDef.declName,
    value     := (← visit preDef.value),
    modifiers := {}
  }

partial def addSmartUnfoldingDef (preDef : PreDefinition) (state : State) : TermElabM Unit := do
  if (← isProp preDef.type) then
    return ()
  else
    let preDefSUnfold ← addSmartUnfoldingDefAux preDef state.matcherBelowDep
    addNonRec preDefSUnfold

end Lean.Elab.Structural
