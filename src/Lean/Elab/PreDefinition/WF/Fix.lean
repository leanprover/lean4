/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Meta.Match.Match
import Lean.Meta.Tactic.Simp.Main
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.Structural.Basic

namespace Lean.Elab.WF
open Meta

private def toUnfold : Std.PHashSet Name :=
  [``measure, ``id, ``Prod.lex, ``invImage].foldl (init := {}) fun s a => s.insert a

private def mkDecreasingProof (decreasingProp : Expr) : TermElabM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar decreasingProp
  let mvarId := mvar.mvarId!
  let ctx ← Simp.Context.mkDefault
  let ctx := { ctx with simpLemmas.toUnfold := toUnfold }
  if let some mvarId ← simpTarget mvarId ctx then
    -- TODO: invoke tactic to close the goal
    trace[Elab.definition.wf] "{MessageData.ofGoal mvarId}"
    admit mvarId
  instantiateMVars mvar

private partial def replaceRecApps (recFnName : Name) (F : Expr) (e : Expr) : TermElabM Expr :=
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
        mkLetFVars #[x] (← loop F (body.instantiate1 x))
    | Expr.mdata d e _   => return mkMData d (← loop F e)
    | Expr.proj n i e _  => return mkProj n i (← loop F e)
    | Expr.app _ _ _ =>
      let processApp (e : Expr) : TermElabM Expr :=
        e.withApp fun f args => do
          if f.isConstOf recFnName && args.size == 1 then
            let r := mkApp F args[0]
            let decreasingProp := (← whnf (← inferType r)).bindingDomain!
            return mkApp r (← mkDecreasingProof decreasingProp)
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
          pure { matcherApp with alts := altsNew }.toExpr
      | none => processApp e
    | e => Structural.ensureNoRecFn recFnName e
  loop F e

def mkFix (preDef : PreDefinition) (wfRel : Expr) : TermElabM PreDefinition := do
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
    let value ← replaceRecApps preDef.declName F (preDef.value.betaRev #[x])
    let value := mkApp wfFix (← mkLambdaFVars #[x, F] value)
    return { preDef with value }

end Lean.Elab.WF
