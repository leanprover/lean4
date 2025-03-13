/-
Copyright (c) 2021 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Data.Array
import Lean.Elab.PreDefinition.Basic
import Lean.Elab.PreDefinition.WF.Basic
import Lean.Elab.Tactic.Basic
import Lean.Meta.ArgsPacker
import Lean.Meta.ForEachExpr
import Lean.Meta.Match.MatcherApp.Transform
import Lean.Meta.Tactic.Cleanup
import Lean.Util.HasConstCache

namespace Lean.Elab.WF
open Meta

register_builtin_option debug.definition.wf.replaceRecApps : Bool := {
    defValue := false
    descr    := "Type check every step of the well-founded definition translation"
  }

/-
Creates a subgoal for a recursive call, as an unsolved `MVar`. The goal is cleaned up, and
the current syntax reference is stored in the `MVar`’s type as a `RecApp` marker, for
use by `solveDecreasingGoals` below.
-/
private def mkDecreasingProof (decreasingProp : Expr) : TermElabM Expr := do
  -- We store the current Ref in the MVar as a RecApp annotation around the type
  let ref ← getRef
  let mvar ← mkFreshExprSyntheticOpaqueMVar (mkRecAppWithSyntax decreasingProp ref)
  let mvarId := mvar.mvarId!
  let _mvarId ← mvarId.cleanup
  return mvar

private partial def replaceRecApps (recFnName : Name) (fixedPrefixSize : Nat) (F : Expr) (e : Expr) : TermElabM Expr := do
  trace[Elab.definition.wf] "replaceRecApps:{indentExpr e}"
  trace[Elab.definition.wf] "type of functorial {F} is{indentExpr (← inferType F)}"
  let e ← loop F e |>.run' {}
  return e
where
  processRec (F : Expr) (e : Expr) : StateRefT (HasConstCache #[recFnName]) TermElabM Expr := do
    if e.getAppNumArgs < fixedPrefixSize + 1 then
      trace[Elab.definition.wf] "replaceRecApp: eta-expanding{indentExpr e}"
      loop F (← etaExpand e)
    else
      let args := e.getAppArgs
      let r := mkApp F (← loop F args[fixedPrefixSize]!)
      let decreasingProp := (← whnf (← inferType r)).bindingDomain!
      let r := mkApp r (← mkDecreasingProof decreasingProp)
      return mkAppN r (← args[fixedPrefixSize+1:].toArray.mapM (loop F))

  processApp (F : Expr) (e : Expr) : StateRefT (HasConstCache #[recFnName]) TermElabM Expr := do
    if e.isAppOf recFnName then
      processRec F e
    else
      e.withApp fun f args => return mkAppN (← loop F f) (← args.mapM (loop F))

  containsRecFn (e : Expr) : StateRefT (HasConstCache #[recFnName]) TermElabM Bool := do
    modifyGet (·.contains e)

  loop (F : Expr) (e : Expr) : StateRefT (HasConstCache #[recFnName]) TermElabM Expr := do
    let e' ← loopGo F e
    if (debug.definition.wf.replaceRecApps.get (← getOptions)) then
      withTransparency .all do withNewMCtxDepth do
        unless (← isTypeCorrect e') do
          throwError "Type error introduced when transforming{indentExpr e}\nto{indentExpr e'}"
        let t1 ← inferType e
        let t2 ← inferType e'
        unless (← isDefEq t1 t2) do
          let (t1, t2) ← addPPExplicitToExposeDiff t1 t2
          throwError "Type not preserved transforming{indentExpr e}\nto{indentExpr e'}\nType was{indentExpr t1}\nand now is{indentExpr t2}"
    return e'

  loopGo (F : Expr) (e : Expr) : StateRefT (HasConstCache #[recFnName]) TermElabM Expr := do
    if !(← containsRecFn e) then
      return e
    match e with
    | Expr.lam n d b c =>
      withLocalDecl n c (← loop F d) fun x => do
        mkLambdaFVars #[x] (← loop F (b.instantiate1 x))
    | Expr.forallE n d b c =>
      withLocalDecl n c (← loop F d) fun x => do
        mkForallFVars #[x] (← loop F (b.instantiate1 x))
    | Expr.letE n type val body _ =>
      withLetDecl n (← loop F type) (← loop F val) fun x => do
        mkLetFVars #[x] (← loop F (body.instantiate1 x)) (usedLetOnly := false)
    | Expr.mdata d b =>
      if let some stx := getRecAppSyntax? e then
        withRef stx <| loop F b
      else
        return mkMData d (← loop F b)
    | Expr.proj n i e => return mkProj n i (← loop F e)
    | Expr.const .. => if e.isConstOf recFnName then processRec F e else return e
    | Expr.app .. =>
      match (← matchMatcherApp? (alsoCasesOn := true) e) with
      | some matcherApp =>
        if let some matcherApp ← matcherApp.addArg? F then
          let altsNew ← (Array.zip matcherApp.alts matcherApp.altNumParams).mapM fun (alt, numParams) =>
            lambdaBoundedTelescope alt numParams fun xs altBody => do
              unless xs.size = numParams do
                throwError "unexpected matcher application alternative{indentExpr alt}\nat application{indentExpr e}"
              let FAlt := xs[numParams - 1]!
              let altBody' ← loop FAlt altBody
              mkLambdaFVars xs altBody'
          return { matcherApp with alts := altsNew, discrs := (← matcherApp.discrs.mapM (loop F)) }.toExpr
        else
          processApp F e
      | none => processApp F e
    | e =>
      ensureNoRecFn #[recFnName] e
      pure e

/-- Refine `F` over `PSum.casesOn` -/
private partial def processSumCasesOn (x F val : Expr) (k : (x : Expr) → (F : Expr) → (val : Expr) → TermElabM Expr) : TermElabM Expr := do
  if x.isFVar && val.isAppOfArity ``PSum.casesOn 6 && val.getArg! 3 == x && (val.getArg! 4).isLambda && (val.getArg! 5).isLambda then
    let args := val.getAppArgs
    let α := args[0]!
    let β := args[1]!
    let FDecl ← F.fvarId!.getDecl
    let (motiveNew, u) ← lambdaTelescope args[2]! fun xs type => do
      let type ← mkArrow (FDecl.type.replaceFVar x xs[0]!) type
      return (← mkLambdaFVars xs type, ← getLevel type)
    let mkMinorNew (ctorName : Name) (minor : Expr) : TermElabM Expr :=
      lambdaBoundedTelescope minor 1 fun xs body => do
        let xNew := xs[0]!
        let FTypeNew := FDecl.type.replaceFVar x (← mkAppOptM ctorName #[α, β, xNew])
        withLocalDeclD FDecl.userName FTypeNew fun FNew => do
          mkLambdaFVars #[xNew, FNew] (← processSumCasesOn xNew FNew body k)
    let minorLeft ← mkMinorNew ``PSum.inl args[4]!
    let minorRight ← mkMinorNew ``PSum.inr args[5]!
    let result := mkAppN (mkConst ``PSum.casesOn [u, (← getLevel α), (← getLevel β)]) #[α, β, motiveNew, x, minorLeft, minorRight, F]
    return result
  else
    k x F val

/-- Refine `F` over `PSigma.casesOn` -/
private partial def processPSigmaCasesOn (x F val : Expr) (k : (F : Expr) → (val : Expr) → TermElabM Expr) : TermElabM Expr := do
  if x.isFVar && val.isAppOfArity ``PSigma.casesOn 5 && val.getArg! 3 == x && (val.getArg! 4).isLambda && (val.getArg! 4).bindingBody!.isLambda then
    let args := val.getAppArgs
    let [_, u, v] := val.getAppFn.constLevels! | unreachable!
    let α := args[0]!
    let β := args[1]!
    let FDecl ← F.fvarId!.getDecl
    let (motiveNew, w) ← lambdaTelescope args[2]! fun xs type => do
      let type ← mkArrow (FDecl.type.replaceFVar x xs[0]!) type
      return (← mkLambdaFVars xs type, ← getLevel type)
    let minor ← lambdaTelescope args[4]! fun xs body => do
        let a := xs[0]!
        let xNew := xs[1]!
        let valNew ← mkLambdaFVars xs[2:] body
        let FTypeNew := FDecl.type.replaceFVar x (← mkAppOptM `PSigma.mk #[α, β, a, xNew])
        withLocalDeclD FDecl.userName FTypeNew fun FNew => do
          mkLambdaFVars #[a, xNew, FNew] (← processPSigmaCasesOn xNew FNew valNew k)
    let result := mkAppN (mkConst ``PSigma.casesOn [w, u, v]) #[α, β, motiveNew, x, minor, F]
    return result
  else
    k F val

private def applyDefaultDecrTactic (mvarId : MVarId) : TermElabM Unit := do
  let remainingGoals ← Tactic.run mvarId do
    applyCleanWfTactic
    Tactic.evalTactic (← `(tactic| decreasing_tactic))
  unless remainingGoals.isEmpty do
    Term.reportUnsolvedGoals remainingGoals

/-
Given an array of MVars, assign MVars with equal type and subsumed local context to each other.
Returns those MVar that did not get assigned.
-/
def assignSubsumed (mvars : Array MVarId) : MetaM (Array MVarId) :=
  mvars.filterPairsM fun mv₁ mv₂ => do
    let mvdecl₁ ← mv₁.getDecl
    let mvdecl₂ ← mv₂.getDecl
    if mvdecl₁.type == mvdecl₂.type then
      -- same goals; check contexts.
        if mvdecl₁.lctx.isSubPrefixOf mvdecl₂.lctx then
          -- mv₁ is better
          mv₂.assign (.mvar mv₁)
          return (true, false)
        if mvdecl₂.lctx.isSubPrefixOf mvdecl₁.lctx then
          -- mv₂ is better
          mv₁.assign (.mvar mv₂)
          return (false, true)
    return (true, true)

/--
The subgoals, created by `mkDecreasingProof`, are of the form `[data _recApp: rel arg param]`, where
`param` is the `PackMutual`'ed parameter of the current function, and thus we can peek at that to
know which function is making the call.
The close coupling with how arguments are packed and termination goals look like is not great,
but it works for now.
-/
def groupGoalsByFunction (argsPacker : ArgsPacker) (numFuncs : Nat) (goals : Array MVarId) : MetaM (Array (Array MVarId)) := do
  let mut r := mkArray numFuncs #[]
  for goal in goals do
    let type ← goal.getType
    let (.mdata _ (.app _ param)) := type
        | throwError "MVar does not look like a recursive call:{indentExpr type}"
    let some (funidx, _) := argsPacker.unpack param
        | throwError "Cannot unpack param, unexpected expression:{indentExpr param}"
    r := r.modify funidx (·.push goal)
  return r

def solveDecreasingGoals (funNames : Array Name) (argsPacker : ArgsPacker) (decrTactics : Array (Option DecreasingBy)) (value : Expr) : MetaM Expr := do
  let goals ← getMVarsNoDelayed value
  let goals ← assignSubsumed goals
  let goalss ← groupGoalsByFunction argsPacker decrTactics.size goals
  for funName in funNames, goals in goalss, decrTactic? in decrTactics do
    Lean.Elab.Term.TermElabM.run' do
    Term.withDeclName funName do
      match decrTactic? with
      | none => do
        for goal in goals do
          let type ← goal.getType
          let some ref := getRecAppSyntax? (← goal.getType)
            | throwError "MVar not annotated as a recursive call:{indentExpr type}"
          withRef ref <| applyDefaultDecrTactic goal
      | some decrTactic => withRef decrTactic.ref do
        unless goals.isEmpty do -- unlikely to be empty
          -- make info from `runTactic` available
          goals.forM fun goal => pushInfoTree (.hole goal)
          let remainingGoals ← Tactic.run goals[0]! do
            Tactic.setGoals goals.toList
            applyCleanWfTactic
            Tactic.withTacticInfoContext decrTactic.ref do
              Tactic.evalTactic decrTactic.tactic
          unless remainingGoals.isEmpty do
            Term.reportUnsolvedGoals remainingGoals
  instantiateMVars value

def mkFix (preDef : PreDefinition) (prefixArgs : Array Expr) (argsPacker : ArgsPacker)
    (wfRel : Expr) (funNames : Array Name) (decrTactics : Array (Option DecreasingBy)) : TermElabM Expr := do
  let type ← instantiateForall preDef.type prefixArgs
  let (wfFix, varName) ← forallBoundedTelescope type (some 1) fun x type => do
    let x := x[0]!
    let α ← inferType x
    let u ← getLevel α
    let v ← getLevel type
    let motive ← mkLambdaFVars #[x] type
    let rel := mkProj ``WellFoundedRelation 0 wfRel
    let wf  := mkProj ``WellFoundedRelation 1 wfRel
    let varName ← x.fvarId!.getUserName -- See comment below.
    return (mkApp4 (mkConst ``WellFounded.fix [u, v]) α motive rel wf, varName)
  forallBoundedTelescope (← whnf (← inferType wfFix)).bindingDomain! (some 2) fun xs _ => do
    let x   := xs[0]!
    -- Remark: we rename `x` here to make sure we preserve the variable name in the
    -- decreasing goals when the function has only one non fixed argument.
    -- This renaming is irrelevant if the function has multiple non fixed arguments. See `process*` functions above.
    let lctx := (← getLCtx).setUserName x.fvarId! varName
    withLCtx' lctx do
      let F   := xs[1]!
      let val := preDef.value.beta (prefixArgs.push x)
      let val ← processSumCasesOn x F val fun x F val => do
        processPSigmaCasesOn x F val (replaceRecApps preDef.declName prefixArgs.size)
      let val ← solveDecreasingGoals funNames argsPacker decrTactics val
      mkLambdaFVars prefixArgs (mkApp wfFix (← mkLambdaFVars #[x, F] val))

end Lean.Elab.WF
