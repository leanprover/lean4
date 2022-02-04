/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Cleanup
import Lean.Elab.Tactic.Basic
import Lean.Elab.RecAppSyntax
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab.WF
open Meta

private def applyDefaultDecrTactic (mvarId : MVarId) : TermElabM Unit := do
  let remainingGoals ← Tactic.run mvarId do
    Tactic.evalTactic (← `(tactic| decreasing_tactic))
  remainingGoals.forM fun mvarId => Term.reportUnsolvedGoals [mvarId]

private def mkDecreasingProof (decreasingProp : Expr) (decrTactic? : Option Syntax) : TermElabM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar decreasingProp
  let mvarId := mvar.mvarId!
  let mvarId ← cleanup mvarId
  match decrTactic? with
  | none => applyDefaultDecrTactic mvarId
  | some decrTactic => Term.runTactic mvarId decrTactic
  instantiateMVars mvar

private partial def replaceRecApps (recFnName : Name) (decrTactic? : Option Syntax) (F : Expr) (e : Expr) : TermElabM Expr :=
  let rec loop (F : Expr) (e : Expr) : TermElabM Expr := do
    match e with
    | Expr.lam n d b c =>
      withLocalDecl n c.binderInfo (← loop F d) fun x => do
        mkLambdaFVars #[x] (← loop F (b.instantiate1 x))
    | Expr.forallE n d b c =>
      withLocalDecl n c.binderInfo (← loop F d) fun x => do
        mkForallFVars #[x] (← loop F (b.instantiate1 x))
    | Expr.letE n type val body _ =>
      withLetDecl n (← loop F type) (← loop F val) fun x => do
        mkLetFVars #[x] (← loop F (body.instantiate1 x)) (usedLetOnly := false)
    | Expr.mdata d b _   =>
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop F b
      else
        return mkMData d (← loop F b)
    | Expr.proj n i e _  => return mkProj n i (← loop F e)
    | Expr.app _ _ _ =>
      let processApp (e : Expr) : TermElabM Expr :=
        e.withApp fun f args => do
          if f.isConstOf recFnName && args.size == 1 then
            let r := mkApp F (← loop F args[0])
            let decreasingProp := (← whnf (← inferType r)).bindingDomain!
            return mkApp r (← mkDecreasingProof decreasingProp decrTactic?)
          else
            return mkAppN (← loop F f) (← args.mapM (loop F))
      let matcherApp? ← matchMatcherApp? e
      match matcherApp? with
      | some matcherApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName 0 e then
          processApp e
        else
          let matcherApp ← mapError (matcherApp.addArg F) (fun msg => "failed to add functional argument to 'matcher' application" ++ indentD msg)
          let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
            lambdaTelescope alt fun xs altBody => do
              unless xs.size >= numParams do
                throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
              let FAlt := xs[numParams - 1]
              mkLambdaFVars xs (← loop FAlt altBody)
          return { matcherApp with alts := altsNew, discrs := (← matcherApp.discrs.mapM (loop F)) }.toExpr
      | none => processApp e
    | e => Structural.ensureNoRecFn recFnName e
  loop F e

/-- Refine `F` over `Sum.casesOn` -/
private partial def processSumCasesOn (x F val : Expr) (k : (x : Expr) → (F : Expr) → (val : Expr) → TermElabM Expr) : TermElabM Expr := do
  if x.isFVar && val.isAppOfArity ``Sum.casesOn 6 && val.getArg! 3 == x && (val.getArg! 4).isLambda && (val.getArg! 5).isLambda then
    let args := val.getAppArgs
    let α := args[0]
    let β := args[1]
    let FDecl ← getLocalDecl F.fvarId!
    let (motiveNew, u) ← lambdaTelescope args[2] fun xs type => do
      let type ← mkArrow (FDecl.type.replaceFVar x xs[0]) type
      return (← mkLambdaFVars xs type, ← getLevel type)
    let mkMinorNew (ctorName : Name) (minor : Expr) : TermElabM Expr :=
      lambdaTelescope minor fun xs body => do
        let xNew := xs[0]
        let valNew ← mkLambdaFVars xs[1:] body
        let FTypeNew := FDecl.type.replaceFVar x (← mkAppOptM ctorName #[α, β, xNew])
        withLocalDeclD FDecl.userName FTypeNew fun FNew => do
          mkLambdaFVars #[xNew, FNew] (← processSumCasesOn xNew FNew valNew k)
    let minorLeft ← mkMinorNew ``Sum.inl args[4]
    let minorRight ← mkMinorNew ``Sum.inr args[5]
    let result := mkAppN (mkConst ``Sum.casesOn [u, (← getDecLevel α), (← getDecLevel β)]) #[α, β, motiveNew, x, minorLeft, minorRight, F]
    return result
  else
    k x F val

/-- Refine `F` over `PSigma.casesOn` -/
private partial def processPSigmaCasesOn (x F val : Expr) (k : (F : Expr) → (val : Expr) → TermElabM Expr) : TermElabM Expr := do
  if x.isFVar && val.isAppOfArity ``PSigma.casesOn 5 && val.getArg! 3 == x && (val.getArg! 4).isLambda && (val.getArg! 4).bindingBody!.isLambda then
    let args := val.getAppArgs
    let [_, u, v] := val.getAppFn.constLevels! | unreachable!
    let α := args[0]
    let β := args[1]
    let FDecl ← getLocalDecl F.fvarId!
    let (motiveNew, w) ← lambdaTelescope args[2] fun xs type => do
      let type ← mkArrow (FDecl.type.replaceFVar x xs[0]) type
      return (← mkLambdaFVars xs type, ← getLevel type)
    let minor ← lambdaTelescope args[4] fun xs body => do
        let a := xs[0]
        let xNew := xs[1]
        let valNew ← mkLambdaFVars xs[2:] body
        let FTypeNew := FDecl.type.replaceFVar x (← mkAppOptM `PSigma.mk #[α, β, a, xNew])
        withLocalDeclD FDecl.userName FTypeNew fun FNew => do
          mkLambdaFVars #[a, xNew, FNew] (← processPSigmaCasesOn xNew FNew valNew k)
    let result := mkAppN (mkConst ``PSigma.casesOn [w, u, v]) #[α, β, motiveNew, x, minor, F]
    return result
  else
    k F val

def mkFix (preDef : PreDefinition) (wfRel : Expr) (decrTactic? : Option Syntax) : TermElabM PreDefinition := do
  let wfFix ← forallBoundedTelescope preDef.type (some 1) fun x type => do
    let x := x[0]
    let α ← inferType x
    let u ← getLevel α
    let v ← getLevel type
    let motive ← mkLambdaFVars #[x] type
    let rel := mkProj ``WellFoundedRelation 0 wfRel
    let wf  := mkProj ``WellFoundedRelation 1 wfRel
    return mkApp4 (mkConst ``WellFounded.fix [u, v]) α motive rel wf
  forallBoundedTelescope (← whnf (← inferType wfFix)).bindingDomain! (some 2) fun xs _ => do
    let x   := xs[0]
    let F   := xs[1]
    let val := preDef.value.betaRev #[x]
    let val ← processSumCasesOn x F val fun x F val => processPSigmaCasesOn x F val (replaceRecApps preDef.declName decrTactic?)
    return { preDef with value := mkApp wfFix (← mkLambdaFVars #[x, F] val) }

end Lean.Elab.WF
