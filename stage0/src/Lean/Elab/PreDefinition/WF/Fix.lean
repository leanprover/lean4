/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Util.HasConstCache
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.Simp.Main
import Lean.Meta.Tactic.Cleanup
import Lean.Elab.Tactic.Basic
import Lean.Elab.RecAppSyntax
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic
import Lean.Elab.PreDefinition.Structural.BRecOn

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

private partial def replaceRecApps (recFnName : Name) (fixedPrefixSize : Nat) (decrTactic? : Option Syntax) (F : Expr) (e : Expr) : TermElabM Expr :=
  loop F e |>.run' {}
where
  processRec (F : Expr) (e : Expr) : StateRefT (HasConstCache recFnName) TermElabM Expr := do
    if e.getAppNumArgs < fixedPrefixSize + 1 then
      loop F (← etaExpand e)
    else
      let args := e.getAppArgs
      let r := mkApp F (← loop F args[fixedPrefixSize])
      let decreasingProp := (← whnf (← inferType r)).bindingDomain!
      let r := mkApp r (← mkDecreasingProof decreasingProp decrTactic?)
      return mkAppN r (← args[fixedPrefixSize+1:].toArray.mapM (loop F))

  processApp (F : Expr) (e : Expr) : StateRefT (HasConstCache recFnName) TermElabM Expr := do
    if e.isAppOf recFnName then
      processRec F e
    else
      e.withApp fun f args => return mkAppN (← loop F f) (← args.mapM (loop F))

  containsRecFn (e : Expr) : StateRefT (HasConstCache recFnName) TermElabM Bool := do
    modifyGet (·.contains e)

  loop (F : Expr) (e : Expr) : StateRefT (HasConstCache recFnName) TermElabM Expr := do
    if !(← containsRecFn e) then
      return e
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
    | Expr.const .. => if e.isConstOf recFnName then processRec F e else return e
    | Expr.app .. =>
      let matcherApp? ← matchMatcherApp? e
      match matcherApp? with
      | some matcherApp =>
        if !Structural.recArgHasLooseBVarsAt recFnName fixedPrefixSize e then
          processApp F e
        else
          let matcherApp ← mapError (matcherApp.addArg F) (fun msg => "failed to add functional argument to 'matcher' application" ++ indentD msg)
          if !(← Structural.refinedArgType matcherApp F) then
            processApp F e
          else
            let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
              lambdaTelescope alt fun xs altBody => do
                unless xs.size >= numParams do
                  throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
                let FAlt := xs[numParams - 1]
                mkLambdaFVars xs (← loop FAlt altBody)
            return { matcherApp with alts := altsNew, discrs := (← matcherApp.discrs.mapM (loop F)) }.toExpr
      | none => processApp F e
    | e => ensureNoRecFn recFnName e

/-- Refine `F` over `PSum.casesOn` -/
private partial def processSumCasesOn (x F val : Expr) (k : (x : Expr) → (F : Expr) → (val : Expr) → TermElabM Expr) : TermElabM Expr := do
  if x.isFVar && val.isAppOfArity ``PSum.casesOn 6 && val.getArg! 3 == x && (val.getArg! 4).isLambda && (val.getArg! 5).isLambda then
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
    let minorLeft ← mkMinorNew ``PSum.inl args[4]
    let minorRight ← mkMinorNew ``PSum.inr args[5]
    let result := mkAppN (mkConst ``PSum.casesOn [u, (← getLevel α), (← getLevel β)]) #[α, β, motiveNew, x, minorLeft, minorRight, F]
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

def mkFix (preDef : PreDefinition) (prefixArgs : Array Expr) (wfRel : Expr) (decrTactic? : Option Syntax) : TermElabM Expr := do
  let type ← instantiateForall preDef.type prefixArgs
  let (wfFix, varName) ← forallBoundedTelescope type (some 1) fun x type => do
    let x := x[0]
    let α ← inferType x
    let u ← getLevel α
    let v ← getLevel type
    let motive ← mkLambdaFVars #[x] type
    let rel := mkProj ``WellFoundedRelation 0 wfRel
    let wf  := mkProj ``WellFoundedRelation 1 wfRel
    let varName := (← getLocalDecl x.fvarId!).userName -- See comment below.
    return (mkApp4 (mkConst ``WellFounded.fix [u, v]) α motive rel wf, varName)
  forallBoundedTelescope (← whnf (← inferType wfFix)).bindingDomain! (some 2) fun xs _ => do
    let x   := xs[0]
    -- Remark: we rename `x` here to make sure we preserve the variable name in the
    -- decreasing goals when the function has only one non fixed argument.
    -- This renaming is irrelevant if the function has multiple non fixed arguments. See `process*` functions above.
    let lctx := (← getLCtx).setUserName x.fvarId! varName
    withTheReader Meta.Context (fun ctx => { ctx with lctx }) do
      let F   := xs[1]
      let val := preDef.value.beta (prefixArgs.push x)
      let val ← processSumCasesOn x F val fun x F val => do
        processPSigmaCasesOn x F val (replaceRecApps preDef.declName prefixArgs.size decrTactic?)
      mkLambdaFVars prefixArgs (mkApp wfFix (← mkLambdaFVars #[x, F] val))

end Lean.Elab.WF
