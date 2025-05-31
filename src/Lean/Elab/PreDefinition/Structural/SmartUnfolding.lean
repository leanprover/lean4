/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Meta.Match.MatcherApp.Basic

namespace Lean.Elab.Structural
open Meta

partial def addSmartUnfoldingDefAux (preDef : PreDefinition) (recArgPos : Nat) : MetaM PreDefinition := do
  return { preDef with
    declName  := mkSmartUnfoldingNameFor preDef.declName
    value     := (← visit preDef.value)
    modifiers := default
  }
where
  /--
     Auxiliary method for annotating `match`-alternatives with `markSmartUnfoldingMatch` and `markSmartUnfoldingMatchAlt`.

     It uses the following approach:
     - Whenever it finds a `match` application `e` s.t. `recArgHasLooseBVarsAt preDef.declName recArgPos e`,
       it marks the `match` with `markSmartUnfoldingMatch`, and each alternative that does not contain a nested marked `match`
       is marked with `markSmartUnfoldingMatchAlt`.

     Recall that the condition `recArgHasLooseBVarsAt preDef.declName recArgPos e` is the one used at `mkBRecOn`.
  -/
  visit (e : Expr) : MetaM Expr := do
    match e with
    | Expr.lam ..     => lambdaTelescope e fun xs b => do mkLambdaFVars xs (← visit b)
    | Expr.forallE .. => forallTelescope e fun xs b => do mkForallFVars xs (← visit b)
    | Expr.letE n type val body _ =>
      withLetDecl n type (← visit val) fun x => do mkLetFVars #[x] (← visit (body.instantiate1 x))
    | Expr.mdata d b     => return mkMData d (← visit b)
    | Expr.proj n i s    => return mkProj n i (← visit s)
    | Expr.app .. =>
      let processApp (e : Expr) : MetaM Expr :=
        e.withApp fun f args =>
          return mkAppN (← visit f) (← args.mapM visit)
      match (← matchMatcherApp? e) with
      | some matcherApp =>
        if !recArgHasLooseBVarsAt preDef.declName recArgPos e then
          processApp e
        else
          let mut altsNew := #[]
          for alt in matcherApp.alts, numParams in matcherApp.altNumParams do
            let altNew ← lambdaBoundedTelescope alt numParams fun xs altBody => do
              unless xs.size = numParams do
                throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
              let altBody ← visit altBody
              let containsSUnfoldMatch := Option.isSome <| altBody.find? fun e => smartUnfoldingMatch? e |>.isSome
              let altBody := if !containsSUnfoldMatch then markSmartUnfoldingMatchAlt altBody else altBody
              mkLambdaFVars xs altBody
            altsNew := altsNew.push altNew
          return markSmartUnfoldingMatch { matcherApp with alts := altsNew }.toExpr
      | _ => processApp e
    | _ => return e

partial def addSmartUnfoldingDef (preDef : PreDefinition) (recArgPos : Nat) : TermElabM Unit := do
  if (← isProp preDef.type) then
    return ()
  else
    withEnableInfoTree false do
      let preDefSUnfold ← addSmartUnfoldingDefAux preDef recArgPos
      let preDefSUnfold ← letToHaveValue preDefSUnfold
      addNonRec preDefSUnfold

end Lean.Elab.Structural
