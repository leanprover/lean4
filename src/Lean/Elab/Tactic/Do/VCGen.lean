/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Std.Do.WP
public import Std.Do.Triple
public import Lean.Elab.Tactic.Simp
public import Lean.Elab.Tactic.Do.ProofMode.Basic
public import Lean.Elab.Tactic.Do.ProofMode.Intro
public import Lean.Elab.Tactic.Do.ProofMode.Revert
public import Lean.Elab.Tactic.Do.ProofMode.Cases
public import Lean.Elab.Tactic.Do.ProofMode.Specialize
public import Lean.Elab.Tactic.Do.ProofMode.Pure
public import Lean.Elab.Tactic.Do.LetElim
public import Lean.Elab.Tactic.Do.Spec
public import Lean.Elab.Tactic.Do.Attr
public import Lean.Elab.Tactic.Do.Syntax
public import Lean.Elab.Tactic.Do.VCGen.Basic
public import Lean.Elab.Tactic.Do.VCGen.Split

public section

namespace Lean.Elab.Tactic.Do

open Lean Parser Elab Tactic Meta Do ProofMode SpecAttr
open Std.Do

private def ProofMode.MGoal.withNewProg (goal : MGoal) (e : Expr) : MGoal :=
  let wpApp := goal.target
  let f := wpApp.getAppFn
  let args := wpApp.getAppArgs
  let wp := args[2]?
  match wp with
  | some (Expr.app rest _) => { goal with target := mkAppN f (args.set! 2 (mkApp rest e)) }
  | _ => goal

namespace VCGen

partial def genVCs (goal : MVarId) (ctx : Context) (fuel : Fuel) : MetaM (Array MVarId) := do
  let (mvar, goal) ← mStartMVar goal
  mvar.withContext <| withReducible do
    let (prf, state) ← StateRefT'.run (ReaderT.run (onGoal goal (← mvar.getTag)) ctx) { fuel }
    mvar.assign prf
    for h : idx in [:state.invariants.size] do
      let mv := state.invariants[idx]
      mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
    for h : idx in [:state.vcs.size] do
      let mv := state.vcs[idx]
      mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag))
    return state.invariants ++ state.vcs
where
  onFail (goal : MGoal) (name : Name) : VCGenM Expr := do
    -- trace[Elab.Tactic.Do.vcgen] "fail {goal.toExpr}"
    emitVC goal.toExpr name

  tryGoal (goal : Expr) (name : Name) : VCGenM Expr := do
    -- trace[Elab.Tactic.Do.vcgen] "tryGoal: {goal}"
    forallTelescope goal fun xs body => do
      let res ← try mStart body catch _ =>
        -- trace[Elab.Tactic.Do.vcgen] "not an MGoal: {body}"
        return ← mkLambdaFVars xs (← emitVC body name)
      -- trace[Elab.Tactic.Do.vcgen] "an MGoal: {res.goal.toExpr}"
      let mut prf ← onGoal res.goal name
      -- res.goal.checkProof prf
      if let some proof := res.proof? then
        prf := mkApp proof prf
      mkLambdaFVars xs prf

  assignMVars (mvars : List MVarId) : VCGenM PUnit := do
    for mvar in mvars do
      if ← mvar.isAssigned then continue
      mvar.withContext <| do
      -- trace[Elab.Tactic.Do.vcgen] "assignMVars {← mvar.getTag}, isDelayedAssigned: {← mvar.isDelayedAssigned},\n{mvar}"
      let ty ← mvar.getType
      if ← isProp ty then
        -- Might contain more `P ⊢ₛ wp⟦prog⟧ Q` apps. Try and prove it!
        mvar.assign (← tryGoal ty (← mvar.getTag))
        return

      if ty.isAppOf ``PostCond || ty.isAppOf ``Invariant || ty.isAppOf ``SPred then
        -- Here we make `mvar` a synthetic opaque goal upon discharge failure.
        -- This is the right call for (previously natural) holes such as loop invariants, which
        -- would otherwise lead to spurious instantiations and unwanted renamings (when leaving the
        -- scope of a local).
        -- But it's wrong for, e.g., schematic variables. The latter should never be PostConds,
        -- Invariants or SPreds, hence the condition.
        mvar.setKind .syntheticOpaque
      addSubGoalAsVC mvar

  onGoal goal name : VCGenM Expr := do
    let T := goal.target
    let T := (← reduceProjBeta? T).getD T -- very slight simplification
    -- trace[Elab.Tactic.Do.vcgen] "target: {T}"
    let goal := { goal with target := T }
    let f := T.getAppFn
    if let .lam binderName .. := f then
      burnOne
      return ← mIntroForall goal ⟨mkIdent (← mkFreshUserName binderName)⟩ (fun g => onGoal g name)
    if f.isLet || f.isConstOf ``SPred.imp then
      burnOne
      return ← mIntro goal (← `(binderIdent| _)) (fun g => onGoal g name)
    if f.isConstOf ``PredTrans.apply then
      return ← onWPApp goal name
    onFail { goal with target := T } name

  onWPApp goal name : VCGenM Expr := ifOutOfFuel (onFail goal name) do
    let args := goal.target.getAppArgs
    let trans := args[2]!
    -- logInfo m!"trans: {trans}"
    let wp ← instantiateMVarsIfMVarApp trans
    let_expr WP.wp m _ps _instWP α e := wp | onFail goal name
    -- NB: e here is a monadic expression, in the "object language"
    let e ← instantiateMVarsIfMVarApp e
    let e := e.headBeta
    let goal := goal.withNewProg e -- to persist the instantiation of `e` and `trans`
    trace[Elab.Tactic.Do.vcgen] "Program: {e}"

    -- let-expressions
    if let .letE x ty val body _nonDep := e.getAppFn' then
      burnOne
      return ← withLetDeclShared (← mkFreshUserName x) ty val fun shared fv leave => do
      let e' := (body.instantiate1 fv).betaRev e.getAppRevArgs
      let info? ← getSplitInfo? e'
      if shared && isJP x && ctx.config.jp && info?.isSome then
        leave (← onJoinPoint fv val (goal.withNewProg e') info?.get! name)
      else
        leave (← onWPApp (goal.withNewProg e') name)

    -- if, dite and match-expressions (without `+jp` which is handled by `onJoinPoint`)
    if let .some info ← getSplitInfo? e then
      return ← onSplit goal info name

    -- zeta-unfold local bindings (TODO don't do this unconditionally)
    let f := e.getAppFn'
    if let some (some val) ← f.fvarId?.mapM (·.getValue?) then
      burnOne
      trace[Elab.Tactic.Do.vcgen] "Call site of {f}"
      if let some info ← knownJP? f.fvarId! then
        return ← onJumpSite (goal.withNewProg e) info
      else
        let e' := val.betaRev e.getAppRevArgs
        return ← onWPApp (goal.withNewProg e') name

    -- delta-unfold definitions according to reducibility and spec attributes,
    -- apply specifications
    if f.isConst then
      burnOne
      -- Now try looking up and applying a spec
      let (prf, specHoles) ← try
        let specThm ← findSpec ctx.specThms wp
        trace[Elab.Tactic.Do.vcgen] "Candidate spec for {f.constName!}: {specThm.proof}"
        withDefault <| collectFreshMVars <| mSpec goal (fun _wp  => return specThm) name
      catch ex =>
        trace[Elab.Tactic.Do.vcgen] "Failed to find spec for {wp}. Trying simp. Reason: {ex.toMessageData}"
        -- Last resort: Simp and try again
        let res ← Simp.simp e
        unless res.expr != e do return ← onFail goal name
        burnOne
        trace[Elab.Tactic.Do.vcgen] "Simplified program to {res.expr}"
        let prf ← onWPApp (goal.withNewProg res.expr) name
        -- context = fun e => H ⊢ₛ wp⟦e⟧ Q
        let context ← withLocalDecl `e .default (mkApp m α) fun e => do
          mkLambdaFVars #[e] (goal.withNewProg e).toExpr
        let res ← Simp.mkCongrArg context res
        return ← res.mkEqMPR prf
      assignMVars specHoles.toList
      return prf
    return ← onFail goal name

  -- Pre: It is `wp⟦e⟧ Q .. := goal.target` and `let .some info ← getSplitInfo? e`, without needing
  --      to instantiate any MVars.
  onSplit (goal : MGoal) (info : SplitInfo) (name : Name)
      (withAltCtx : Nat → Array Expr → VCGenM Expr → VCGenM Expr := fun _ _ k => k) : VCGenM Expr := do
    let args := goal.target.getAppArgs
    let_expr WP.wp m _ps _instWP α e := args[2]! | throwError "Expected wp⟦e⟧ Q in goal.target, got {goal.target}"
    -- Bring into simp NF
    let e ← -- returns/continues only if old e is defeq to new e
      if let .some res ← info.simpDiscrs? e then
        burnOne
        let prf ← onWPApp (goal.withNewProg res.expr) name
        -- context = fun e => H ⊢ₛ wp⟦e⟧ Q
        let context ← withLocalDecl `e .default (mkApp m α) fun e => do
          mkLambdaFVars #[e] (goal.withNewProg e).toExpr
        let res ← Simp.mkCongrArg context res
        res.mkEqMPR prf
      else
        pure e
    -- Try reduce the matcher
    let e ← match (← reduceMatcher? e) with
      | .reduced e' =>
      burnOne
      return ← onWPApp (goal.withNewProg e') name
      | .stuck _ => pure e
      | _ => pure e
    -- throwError "Here we are {args}"
    -- Last resort: Split match
    trace[Elab.Tactic.Do.vcgen] "split match: {e}"
    burnOne
    -- context = fun e => H ⊢ₛ wp⟦e⟧ Q
    let context ← withLocalDecl `e .default (mkApp m α) fun e => do
      mkLambdaFVars #[e] (goal.withNewProg e).toExpr
    return ← info.splitWithConstantMotive goal.toExpr (useSplitter := true) fun altSuff idx params => do
      let res ← liftMetaM <| rwIfOrMatcher idx e
      let goal' := goal.withNewProg res.expr
      let prf ← withAltCtx idx params <| onWPApp goal' (name ++ altSuff)
      let res ← Simp.mkCongrArg context res
      res.mkEqMPR prf

  -- Pre: We had `let x = zetadVal; e`, scoped through `x` as `fv` and have `goal.target = wp⟦e⟧ Q`,
  --      where `e` is a splitter with `SplitInfo` `info`.
  onJoinPoint (fv : Expr) (zetadVal : Expr) (goal : MGoal) (info : SplitInfo) (name : Name) : VCGenM Expr := do
    burnOne
    let args := goal.target.getAppArgs
    let_expr c@WP.wp m ps instWP α e := args[2]! | throwError "Expected wp⟦e⟧ Q in goal.target, got {goal.target}"
    trace[Elab.Tactic.Do.vcgen] "Join point {fv} with matcher {e.getAppFn}"
    let .some resTy := info.resTy | throwError "Encountered dependent motive of {e} despite there being a join point."
    let [uWP, _] := c.constLevels! | throwError "PredTrans.apply has wrong number of levels"
    let σs := mkApp (mkConst ``PostShape.args [uWP]) ps
    let joinTy ← inferType fv
    let numJoinParams ← getNumJoinParams joinTy resTy

    let hypsTys ← forallBoundedTelescope joinTy numJoinParams fun joinArgs _body => do
      let mut hypsTys := #[]
      for (numParams, alt) in info.altInfos do
        -- When the joinTy looks like `(x1 : α1) → ... → (xN : αN) → resTy`,
        -- and the alt looks like `fun (p1 : β1) (pM : βM) => e[p1, ..., pM] : resTy)`,
        -- this will produce type
        --   `(x1 : α1) → ... → (xN : αN) → (p1 : β1) → ... → (pM : βM) → Prop`.
        -- For `dite` and `jp : Nat → Unit → Id Nat`, this will be
        --   `(x : Nat) → (y : Unit) → (h : condTy) → Prop` and
        -- and
        --   `(x : Nat) → (y : Unit) → (h : ¬condTy) → Prop`
        -- For `ite` and `jp : Nat → Unit → Id Nat`, this will be
        --   `(x : Nat) → (y : Unit) → Prop` and
        -- and
        --   `(x : Nat) → (y : Unit) → Prop`
        -- For `match d with | some z => ... | none => ...` and `jp : Nat → Unit → Id Nat`, this will be
        --   `(x : Nat) → (y : Unit) → (z : Nat) → Prop` and
        -- and
        --   `(x : Nat) → (y : Unit) → (z : Unit) → Prop`
        hypsTys := hypsTys.push <| ← lambdaBoundedTelescope alt numParams fun altParams _body =>
          mkForallFVars (joinArgs ++ altParams) (mkSort .zero)
      return hypsTys

    let hypsMVars ← hypsTys.mapIdxM fun i hypsTy =>
      mkFreshExprSyntheticOpaqueMVar hypsTy (name.appendIndexAfter i)

    let (joinPrf, joinGoal) ← forallBoundedTelescope joinTy numJoinParams fun joinParams _body => do
      let φ ← info.splitWithConstantMotive (mkSort .zero) fun _suff idx altParams =>
        return mkAppN hypsMVars[idx]! (joinParams ++ altParams)
      withLocalDecl (← mkFreshUserName `h) .default φ fun h => do
        -- NB: `mkJoinGoal` is not quite `goal.withNewProg` because we only take 4 args and clear
        -- the stateful hypothesis of the goal.
        let mkJoinGoal (e : Expr) :=
          let wp := mkApp5 c m ps instWP α e
          let args := args.set! 2 wp |>.take 4
          let target := mkAppN (mkConst ``PredTrans.apply [uWP]) args
          { u := uWP, σs, hyps := emptyHyp uWP σs, target : MGoal }

        let joinPrf ← mkLambdaFVars (joinParams.push h) (← onWPApp (mkJoinGoal (mkAppN fv joinParams)) name)
        let joinGoal ← mkForallFVars (joinParams.push h) (mkJoinGoal (zetadVal.beta joinParams)).toExpr
        -- `joinPrf : joinGoal` by zeta
        return (joinPrf, joinGoal)

    withLetDecl (← mkFreshUserName `joinPrf) joinGoal joinPrf (kind := .implDetail) fun joinPrf => do
      let prf ← onSplit goal info name fun idx params doGoal => do
        let altLCtxIdx := (← getLCtx).numIndices
        let info : JumpSiteInfo := {
          numJoinParams,
          altParams := params,
          altIdx := idx,
          altLCtxIdx,
          hyps := hypsMVars[idx]!.mvarId!,
          joinPrf,
        }
        withJP fv.fvarId! info doGoal
      mkLetFVars #[joinPrf] prf

  onJumpSite (goal : MGoal) (info : JumpSiteInfo) : VCGenM Expr := do
    let args := goal.target.getAppArgs
    let_expr c@WP.wp _m ps _instWP _α e := args[2]! | throwError "Expected wp⟦e⟧ Q in goal.target, got {goal.target}"
    let [uWP, _] := c.constLevels! | throwError "PredTrans.apply has wrong number of levels"
    let σs := mkApp (mkConst ``PostShape.args [uWP]) ps
    -- Try to frame as many hypotheses as possible into the local context so that they end up
    -- in the shared precondition of the join point spec.
    return ← mTryFrame goal fun goal => do
    -- We need to revert excess state args (any expression `s` in `H[s] ⊢ₛ wp⟦jp x y z⟧ Q s`)
    -- so that goal.hyps has type `Assertion (PredShape.args ps)` and we can use
    -- `joinPrf (h : φ') : ⊢ₛ wp⟦jp a b c⟧ Q` to construct a proof.
    -- Note that we discard `goal.hyps` anyway, so users won't observe anything.
    return ← mRevertForallN goal (args.size - 4) (← mkFreshUserName `_) fun goal => do
    let joinArgs := e.getAppArgs
    let newLocalDecls := (← getLCtx).decls.foldl (init := #[]) (start := info.altLCtxIdx) Array.push
      |>.filterMap id
      |>.filter (not ·.isImplementationDetail)
    let newLocals := newLocalDecls.map LocalDecl.toExpr
    let altParams := info.altParams
    trace[Elab.Tactic.Do.vcgen] "altParams: {altParams}, newLocals: {newLocals}"
    let (φ, prf) ← forallBoundedTelescope (← info.hyps.getType) info.numJoinParams fun joinParams _prop => do
      trace[Elab.Tactic.Do.vcgen] "joinParams: {joinParams}, actual joinParams: {e.getAppArgs}"
      let eqs ← liftMetaM <| joinParams.zipWithM mkEq joinArgs
      let φ := mkAndN eqs.toList
      let prf ← mkAndIntroN (← liftMetaM <| joinArgs.mapM mkEqRefl).toList
      let φ := φ.abstract newLocals
      -- Invariant: `prf : (fun joinParams => φ) joinArgs`
      let (_, φ, prf) ← newLocalDecls.foldrM (init := (newLocals, φ, prf)) fun decl (locals, φ, prf) => do
        let locals := locals.pop
        match decl.value? with
        | some v =>
          let type := decl.type.abstract locals
          let val := v.abstract locals
          let φ := mkLet decl.userName type val φ (nondep := decl.isNondep)
          return (locals, φ, prf)
        | none =>
          let type := decl.type.abstract locals
          let u ← getLevel type
          let ψ := mkLambda decl.userName decl.binderInfo type φ
          let φ := mkApp2 (mkConst ``Exists [u]) type ψ
          let prf := mkApp4 (mkConst ``Exists.intro [u]) type ψ decl.toExpr prf
          return (locals, φ, prf)

      -- Abstract φ over the altParams in order to instantiate info.hyps below
      let φ ←
        if altParams == #[mkConst ``Unit.unit] then -- See `Match.forallAltVarsTelescope`
          pure <| mkLambda `_ .default (mkConst ``Unit) φ
        else
          mkLambdaFVars altParams φ
      return (← mkLambdaFVars joinParams φ, ← mkLambdaFVars joinParams prf)
    info.hyps.assign φ
    let φ := φ.beta (joinArgs ++ altParams)
    let prf := prf.beta joinArgs
    let jumpPrf := mkAppN info.joinPrf joinArgs
    let jumpGoal ← inferType jumpPrf
    let .forallE _ φ' .. := jumpGoal | throwError "jumpGoal {jumpGoal} is not a forall"
    trace[Elab.Tactic.Do.vcgen] "φ applied: {φ}, prf applied: {prf}, type: {← inferType prf}"
    let rwPrf ← rwIfOrMatcher info.altIdx φ'
    trace[Elab.Tactic.Do.vcgen] "joinPrf: {← inferType info.joinPrf}"
    let jumpPrf := mkAppN info.joinPrf (joinArgs.push (← rwPrf.mkEqMPR prf))
    let prf₁ := mkApp2 (mkConst ``SPred.true_intro [uWP]) σs goal.hyps
    let prf ← mkAppM ``SPred.entails.trans #[prf₁, jumpPrf]
    -- goal.checkProof prf
    return prf

end VCGen

@[builtin_tactic Lean.Parser.Tactic.mvcgen]
def elabMVCGen : Tactic := fun stx => withMainContext do
  if mvcgen.warning.get (← getOptions) then
    logWarningAt stx "The `mvcgen` tactic is experimental and still under development. Avoid using it in production projects."
  let ctx ← mkSpecContext stx[1] stx[2]
  let fuel := match ctx.config.stepLimit with
    | some n => .limited n
    | none => .unlimited
  let goal ← getMainGoal
  let goal ← if ctx.config.elimLets then elimLets goal else pure goal
  let vcs ← VCGen.genVCs goal ctx fuel
  let runOnVCs (tac : TSyntax `tactic) (vcs : Array MVarId) : TermElabM (Array MVarId) :=
    vcs.flatMapM fun vc => List.toArray <$> Term.withSynthesize do
      Tactic.run vc (Tactic.evalTactic tac *> Tactic.pruneSolvedGoals)
  let vcs ← Term.TermElabM.run' do
    let vcs ← if ctx.config.trivial then runOnVCs (← `(tactic| try mvcgen_trivial)) vcs else pure vcs
    let vcs ← if ctx.config.leave then runOnVCs (← `(tactic| try mleave)) vcs else pure vcs
    return vcs
  -- Eliminating lets here causes some metavariables in `mkFreshPair_triple` to become nonassignable
  -- so we don't do it. Presumably some weird delayed assignment thing is going on.
  -- let vcs ← if ctx.config.elimLets then liftMetaM <| vcs.mapM elimLets else pure vcs
  replaceMainGoal vcs.toList
