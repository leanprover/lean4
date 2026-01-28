/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public meta import Lean.Elab.Tactic.Do.VCGen.Split
public meta import Lean.Elab.Tactic.Simp
public meta import Lean.Elab.Tactic.Do.ProofMode.MGoal
public meta import Lean.Elab.Tactic.Do.ProofMode.Revert
public meta import Lean.Elab.Tactic.Do.ProofMode.Cases
public meta import Lean.Elab.Tactic.Do.ProofMode.Specialize
public meta import Lean.Elab.Tactic.Do.LetElim
public meta import Lean.Elab.Tactic.Do.Spec
public meta import Lean.Elab.Tactic.Do.Syntax
public meta import Lean.Elab.Tactic.Induction
public meta import Lean.Elab.Tactic.Do.VCGen.Basic
public meta import Lean.Elab.Term.TermElabM
public meta import Lean.Elab.Tactic.Do.VCGen.Basic
public meta import Lean.Elab.Tactic.Do.VCGen.SuggestInvariant
public meta import Lean.Meta.Tactic.TryThis
public meta import Lean.Elab.Tactic.Do.LetElim
public meta import Lean.Meta.Sym

namespace Lean.Elab.Tactic.Do

open Lean Parser Elab Tactic Meta Sym Do ProofMode SpecAttr
open Std.Do

meta section

def ProofMode.MGoal.withNewProg (goal : MGoal) (e : Expr) : MGoal :=
  let wpApp := goal.target
  let f := wpApp.getAppFn
  let args := wpApp.getAppArgs
  let wp := args[2]?
  match wp with
  | some (Expr.app rest _) => { goal with target := mkAppN f (args.set! 2 (mkApp rest e)) }
  | _ => goal

def mkProj' (n : Name) (i : Nat) (Q : Expr) : MetaM Expr := do
  return (← projectCore? Q i).getD (mkProj n i Q)

mutual
meta partial def dischargePostEntails (α : Expr) (ps : Expr) (Q : Expr) (Q' : Expr) : MetaM Expr := do
  -- Often, Q' is fully instantiated while Q contains metavariables. Try refl
  let u ← liftMetaM <| getLevel α >>= decLevel
  if (← withDefault <| isDefEqGuarded Q Q') then
    return mkApp3 (mkConst ``PostCond.entails.refl [u]) α ps Q'
  let Q ← whnfR Q
  let Q' ← whnfR Q'
  -- If Q (postcond of the spec) is just an fvar, we do not decompose further
  if let some _fvarId := Q.fvarId? then
    return ← mkFreshExprSyntheticOpaqueMVar (mkApp4 (mkConst ``PostCond.entails [u]) α ps Q Q')
  -- Otherwise decompose the conjunction
  let prf₁ ← withLocalDeclD (← liftMetaM <| mkFreshUserName `r) α fun a => do
    let Q1a := (← mkProj' ``Prod 0 Q).betaRev #[a]
    let Q'1a := (← mkProj' ``Prod 0 Q').betaRev #[a]
    let σs := mkApp (mkConst ``PostShape.args [u]) ps
    let uniq ← liftMetaM mkFreshId
    let name ← liftMetaM <| mkFreshUserName `h
    let goal := MGoal.mk u σs (Hyp.mk name uniq Q1a).toExpr Q'1a
    mkLambdaFVars #[a] (← mkFreshExprSyntheticOpaqueMVar goal.toExpr)
  let prf₂ ← dischargeFailEntails u ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q')
  mkAppM ``And.intro #[prf₁, prf₂]

partial def dischargeFailEntails (u : Level) (ps : Expr) (Q : Expr) (Q' : Expr) : MetaM Expr := do
  if ps.isAppOf ``PostShape.pure then
    return mkConst ``True.intro
  if ← withDefault <| isDefEqGuarded Q Q' then
    return mkApp2 (mkConst ``ExceptConds.entails.refl [u]) ps Q
  if ← withDefault <| isDefEqGuarded Q (mkApp (mkConst ``ExceptConds.false [u]) ps) then
    return mkApp2 (mkConst ``ExceptConds.entails_false [u]) ps Q'
  if ← withDefault <| isDefEqGuarded Q' (mkApp (mkConst ``ExceptConds.true [u]) ps) then
    return mkApp2 (mkConst ``ExceptConds.entails_true [u]) ps Q
  -- the remaining cases are recursive.
  if let some (_σ, ps) := ps.app2? ``PostShape.arg then
    return ← dischargeFailEntails u ps Q Q'
  if let some (ε, ps) := ps.app2? ``PostShape.except then
    let Q ← whnfR Q
    let Q' ← whnfR Q'
    let prf₁ ← withLocalDeclD (← liftMetaM <| mkFreshUserName `e) ε fun e => do
      let Q1e := (← mkProj' ``Prod 0 Q).betaRev #[e]
      let Q'1e := (← mkProj' ``Prod 0 Q').betaRev #[e]
      let σs := mkApp (mkConst ``PostShape.args [u]) ps
      let uniq ← liftMetaM mkFreshId
      let goal := MGoal.mk u σs (Hyp.mk (← liftMetaM <| mkFreshUserName `h) uniq Q1e).toExpr Q'1e
      mkLambdaFVars #[e] (← mkFreshExprSyntheticOpaqueMVar goal.toExpr)
    let prf₂ ← dischargeFailEntails u ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q')
    return ← mkAppM ``And.intro #[prf₁, prf₂] -- This is just a bit too painful to construct by hand
  -- This case happens when decomposing with unknown `ps : PostShape`
  mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``ExceptConds.entails [u]) ps Q Q')
end

def dischargeMGoal (goal : MGoal) : MetaM Expr := do
  liftMetaM <| do trace[Elab.Tactic.Do.spec] "dischargeMGoal: {goal.target}"
  -- We try to discharge trivial goals by rfl and And.intro directly. Doing so may instantiate
  -- schematic variables from the spec and that is really important for generating fewer and smaller
  -- VCs.
  let some prf ← liftMetaM <| goal.pureRflAndAndIntro
    | mkFreshExprSyntheticOpaqueMVar goal.toExpr
  liftMetaM <| do trace[Elab.Tactic.Do.spec] "proof: {prf}"
  return prf

def mkPatternCore (type : Expr) (levelParams : List Name) (varTypes : Array Expr) (pattern : Expr) : MetaM Pattern := do
  let fnInfos ← mkProofInstInfoMapFor pattern
  let checkTypeMask := mkCheckTypeMask pattern varTypes.size
  let checkTypeMask? := if checkTypeMask.all (· == false) then none else some checkTypeMask
  let varInfos? ← forallBoundedTelescope type varTypes.size fun xs _ =>
    mkProofInstArgInfo? xs
  return { levelParams, varTypes, pattern, fnInfos, varInfos?, checkTypeMask? }

public def mkPatternFromExpr (h : Expr) (num? : Option Nat := none) : MetaM Pattern := do
  let type ← inferType h
  let type ← preprocessType type
  let hugeNumber := 10000000
  let num := num?.getD hugeNumber
  let rec go (i : Nat) (pattern : Expr) (varTypes : Array Expr) : MetaM Pattern := do
    if i < num then
      if let .forallE _ d b _ := pattern then
        return (← go (i+1) b (varTypes.push d))
    mkPatternCore type [] varTypes pattern
  go 0 type #[]

def _root_.Lean.Elab.Tactic.Do.SpecAttr.SpecProof.mkBackwardRule (proof : SpecProof) : MetaM BackwardRule := do
  match proof with
  | .global declName => mkBackwardRuleFromDecl declName
  | _ => throwError "mkBackwardRule: {proof} not supported yet"

def _root_.Lean.Elab.Tactic.Do.SpecAttr.SpecProof.mkProofWithLevelParams (proof : SpecProof) : MetaM (Expr × List Level) := do
  match proof with
  | .global declName =>
    let e ← mkConstWithLevelParams declName
    return (e, e.constLevels!)
  | .local h => return (mkFVar h, [])
  | .stx _ _ proof => return (proof, [])

/--
Creates a value to assign to input goal metavariable using unification result.

Handles both constant expressions (common case, avoids `instantiateLevelParams`)
and general expressions.
-/
def mkValue (expr : Expr) (pattern : Pattern) (result : MatchUnifyResult) : Expr :=
  if let .const declName [] := expr then
    mkAppN (mkConst declName result.us) result.args
  else
    mkAppN (expr.instantiateLevelParams pattern.levelParams result.us) result.args

def _root_.Lean.Elab.Tactic.Do.SpecAttr.SpecProof.mkValue (proof : SpecProof) (result : MatchUnifyResult) : MetaM Expr :=
  match proof with
  | .global declName => return mkAppN (mkConst declName result.us) result.args
  | _ => throwError "mkBackwardRule: {proof} not supported yet"

/--
  Returns the proof and the list of new unassigned MVars.
-/
def mSpecSimple (goal : MGoal) (specThm : SpecTheorem) : SymM Expr := do
  /-
  We build a proof of the form
  ```
  theorem ext2 [WP m (.arg σ₁ (.arg σ₂ ps))] {α : Type u} {x : m α} {P : Assertion ps} {P' : Assertion (.arg σ₁ (.arg σ₂ ps))} {Q Q' : PostCond α (.arg σ₁ (.arg σ₂ ps))}
      (h : Triple x P' Q') (hpre : P ⊢ₛ P' s₁ s₂) (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q s₁ s₂ := by
    apply SPred.entails.trans hpre
    apply SPred.entails.trans (Triple.iff.mp h s₁ s₂)
    apply (wp x).mono _ _ hpost s₁ s₂
  ```
  Where `s₁` and `s₂` are the excess arguments to the target `wp⟦x⟧ Q` application.
  -/
  let T := goal.target.consumeMData  -- `wp⟦x⟧ Q s₁ s₂`
  unless T.getAppFn.constName! == ``PredTrans.apply do
    liftMetaM (throwError "target not a PredTrans.apply application {indentExpr T}")
  let wp := T.getArg! 2
  let args := T.getAppArgs
  let P := goal.hyps
  let Q := args[3]!
  let excessArgs := (args.extract 4 args.size).reverse  -- `#[s₁, s₂]`

  -- Create a backward rule for the spec we look up in the database
  let (spec, specUs) ← specThm.proof.mkProofWithLevelParams
  forallTelescope (← Meta.inferType spec) fun schematicVars specTy => do
    let spec := mkAppN spec schematicVars
    let_expr f@Triple m ps instWP α prog P' Q' := specTy
      | liftMetaM <| throwError "The type of spec `{spec}` is not a Triple application: {indentExpr specTy}"
    let u := f.constLevels![0]! -- TODO this is wrong when it's a level parameter of the spec. It should be instantiated to goal.u
    let P'args := mkAppN P' excessArgs
    withLocalDeclD (← mkFreshUserName `hpre) (mkApp3 (mkConst ``SPred.entails [u]) goal.σs P P'args) fun hpre => do
    withLocalDeclD (← mkFreshUserName `hpost) (mkApp4 (mkConst ``PostCond.entails [u]) ps α Q' Q) fun hpost => do
    let prf := mkApp6 (mkConst ``PredTrans.mono [u]) ps α wp Q Q' hpost
    let specPrf := mkApp4 (mkConst ``Triple.iff [u]) ps α wp Q Q' hpost
    return mkApp6 (mkConst ``SPred.entails.trans [u]) goal.σs P (mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog) (mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog) hpre hpost
    -- prog should be x
    let wp' := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog
    let wpPat := { specPat with pattern := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog }
    let PPat := { specPat with pattern := P }
    let QPat := { specPat with pattern := Q }


  -- Instantiation creates `.natural` MVars, which possibly get instantiated by the def eq checks
  -- below when they occur in `P` or `Q`.
  -- That's good for many such as MVars ("schematic variables"), but problematic for MVars
  -- corresponding to `Invariant`s, which should end up as user goals.
  -- To prevent accidental instantiation, we mark all `Invariant` MVars as synthetic opaque.
  -- Ignore this for now.
  -- for mvar in mvars do
  --   let ty ← mvar.mvarId!.getType
  --   if ty.isAppOf ``Invariant then mvar.mvarId!.setKind .syntheticOpaque

  -- Actually instantiate the specThm using the expected type computed from `wp`.
  let_expr f@Triple m ps instWP α prog P Q := specPat.pattern
    | liftMetaM <| throwError "target not a Triple application {specPat.pattern}"
  let wp' := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog
  let wpPat := { specPat with pattern := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog }
  let PPat := { specPat with pattern := P }
  let QPat := { specPat with pattern := Q }
  let some result ← wpPat.match? wp
    | throwError "Failed to match spec pattern {wpPat.pattern} with target {wp}"

  -- TODO: I think the Pattern machinery does this for us already.
  -- Try synthesizing synthetic MVars. We don't have the convenience of `TermElabM`, hence
  -- this poor man's version of `TermElabM.synthesizeSyntheticMVars`.
  -- We do so after the def eq call so that instance resolution is likely to succeed.
  -- If it _doesn't_ succeed now, then the spec theorem leaves behind an additional subgoal.
  -- We'll add a trace message if that happens.
  -- for mvar in mvars do
  --   let mvar := mvar.mvarId!
  --   if (← mvar.getKind) matches .synthetic && !(← liftMetaM <| mvar.isAssigned) then
  --     match ← trySynthInstance (← mvar.getType) with
  --     | .some prf => liftMetaM <| mvar.assign prf
  --     | .none => continue
  --     | .undef => liftMetaM <| do
  --       trace[Elab.Tactic.Do.spec] "Failed to synthesize synthetic MVar {mvar} from unifying {specTy} against {prog}.\n\
  --         This likely leaves behind an additional subgoal."

  let P ← instantiateMVarsIfMVarApp P
  let Q ← instantiateMVarsIfMVarApp Q

  let P := P.betaRev excessArgs
  let spec := spec.betaRev excessArgs
  let u := goal.u

  -- Often P or Q are schematic (i.e. an MVar app). Try to solve by rfl.
  -- We do `fullApproxDefEq` here so that `constApprox` is active; this is useful in
  -- `need_const_approx` of `doLogicTests.lean`.
  -- TODO: Use SymM here
  let (HPRfl, QQ'Rfl) ← withDefault <| fullApproxDefEq <| do
    return (← isDefEqGuarded P goal.hyps, ← isDefEqGuarded Q Q')

  -- Discharge the validity proof for the spec if not rfl
  -- TODO: Use SymM here
  let mut prePrf : Expr → Expr := id
  if !HPRfl then
    -- let P := (← reduceProjBeta? P).getD P
    -- Try to avoid creating a longer name if the postcondition does not need to create a goal
    let HPPrf ← dischargeMGoal { goal with target := P }
    prePrf := mkApp6 (mkConst ``SPred.entails.trans [u]) goal.σs goal.hyps P goal.target HPPrf

  -- Discharge the entailment on postconditions if not rfl
  -- TODO: Use SymM here
  let mut postPrf : Expr → Expr := id
  if !QQ'Rfl then
    -- Try to avoid creating a longer name if the precondition does not need to create a goal
    let wpApplyQ  := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q  -- wp⟦x⟧.apply Q; that is, T without excess args
    let wpApplyQ' := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q' -- wp⟦x⟧.apply Q'
    let QQ' ← dischargePostEntails α ps Q Q'
    let QQ'mono := mkApp6 (mkConst ``PredTrans.mono [u]) ps α wp Q Q' QQ'
    postPrf := fun h =>
      mkApp6 (mkConst ``SPred.entails.trans [u]) goal.σs P (wpApplyQ.betaRev excessArgs) (wpApplyQ'.betaRev excessArgs)
        h (QQ'mono.betaRev excessArgs)

  -- finally build the proof; HPPrf.trans (spec.trans QQ'mono)
  return prePrf (postPrf spec)

namespace VCGen

public structure Result where
  invariants : Array MVarId
  vcs : Array MVarId

public meta partial def genVCs (goal : MVarId) (ctx : Context) (fuel : Fuel) : MetaM Result := do
  let (mvar, goal) ← mStartMVar goal
  mvar.withContext <| withReducible do
    let (prf, state) ← StateRefT'.run (ReaderT.run (onGoal goal (← mvar.getTag)) ctx) { fuel }
    mvar.assign prf
    for h : idx in [:state.invariants.size] do
      let mv := state.invariants[idx]
      mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
    for h : idx in [:state.vcs.size] do
      let mv := state.vcs[idx]
      mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
    return { invariants := state.invariants, vcs := state.vcs }
where
  onFail (goal : MGoal) (name : Name) : VCGenM Expr := do
    -- trace[Elab.Tactic.Do.vcgen] "fail {goal.toExpr}"
    emitVC goal.toExpr name

  tryGoal (mvar : MVarId) : OptionT VCGenM Expr := mvar.withContext do
    -- The type might contain more `P ⊢ₛ wp⟦prog⟧ Q` apps. Try and prove it!
    forallTelescope (← mvar.getType) fun xs body => do
      let res ← try mStart body catch _ => OptionT.fail
      -- trace[Elab.Tactic.Do.vcgen] "an MGoal: {res.goal.toExpr}, {xs}"
      let mut prf ← onGoal res.goal (← mvar.getTag)
      -- res.goal.checkProof prf
      if let some proof := res.proof? then
        prf := mkApp proof prf
      return ← mkLambdaFVars xs prf

  assignMVars (mvars : List MVarId) : VCGenM PUnit := do
    for mvar in mvars do
      if ← mvar.isAssigned then continue
      -- trace[Elab.Tactic.Do.vcgen] "assignMVars {← mvar.getTag}, isDelayedAssigned: {← mvar.isDelayedAssigned},\n{mvar}"
      let some prf ← (tryGoal mvar).run | addSubGoalAsVC mvar
      if ← mvar.isAssigned then
        throwError "Tried to assign already assigned metavariable `{← mvar.getTag}`. MVar: {mvar}\nAssignment: {mkMVar mvar}\nNew assignment: {prf}"
      mvar.assign prf

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
    let wp ← instantiateMVarsIfMVarApp trans
    let_expr WP.wp m _ps _instWP α e := wp | onFail goal name
    -- NB: e here is a monadic expression, in the "object language"
    let e ← instantiateMVarsIfMVarApp e
    let e := e.headBeta
    let goal := goal.withNewProg e -- to persist the instantiation of `e` and `trans`
    withTraceNode `Elab.Tactic.Do.vcgen (msg := fun _ => return m!"Program: {e}") do

    -- let-expressions
    if let .letE x ty val body _nonDep := e.getAppFn' then
      burnOne
      return ← withLetDeclShared (← mkFreshUserName x) ty val fun shared fv leave => do
      let e' := (body.instantiate1 fv).betaRev e.getAppRevArgs
      leave (← onWPApp (goal.withNewProg e') name)

    -- if, dite and match-expressions
    if let .some info ← getSplitInfo? e then
      return ← onSplit goal info name

    -- zeta-unfold local bindings (TODO don't do this unconditionally)
    let f := e.getAppFn'
    if let some (some val) ← f.fvarId?.mapM (·.getValue?) then
      burnOne
      trace[Elab.Tactic.Do.vcgen] "Call site of {f}"
      let e' := val.betaRev e.getAppRevArgs
      return ← onWPApp (goal.withNewProg e') name

    -- delta-unfold definitions according to reducibility and spec attributes,
    -- apply specifications
    if f.isConst || f.isFVar then
      burnOne
      -- Now try looking up and applying a spec
      let (prf, specHoles) ← try
        let specThm ← findSpec (← read).specThms wp
        trace[Elab.Tactic.Do.vcgen] "Candidate spec for {f}: {specThm.proof}"
        -- We eta-expand as far here as goal.σs permits.
        -- This is so that `mSpec` can frame hypotheses involving uninstantiated loop invariants.
        -- It is absolutely crucial that we do not lose these hypotheses in the inductive step.
        collectFreshMVars <| mIntroForallN goal (← TypeList.length goal.σs) fun goal =>
          mSpecSimple goal specThm
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
      trace[Elab.Tactic.Do.vcgen] "Unassigned specHoles: {(← specHoles.filterM (not <$> ·.isAssigned)).map fun m => (m.name, mkMVar m)}"
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
        return ← res.mkEqMPR prf
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
    return ← info.splitWith goal.toExpr (useSplitter := true) fun altSuff expAltType idx params => do
      burnOne
      let e ← mkFreshExprMVar (mkApp m α)
      unless ← isDefEq (goal.withNewProg e).toExpr expAltType do
        throwError "The alternative type {expAltType} returned by `splitWith` does not match {(goal.withNewProg e).toExpr}. This is a bug in `mvcgen`."
      let e ← instantiateMVarsIfMVarApp e
      let res ← liftMetaM <| rwIfOrMatcher idx e
      -- When `FunInd.rwMatcher` fails, it returns the original expression. We'd loop in that case,
      -- so we rather throw an error.
      if res.expr == e then
        throwError "`rwMatcher` failed to rewrite {indentExpr e}\n\
          Check the output of `trace.Elab.Tactic.Do.vcgen.split` for more info and submit a bug report."
      let goal' := goal.withNewProg res.expr
      let prf ← withAltCtx idx params <| onWPApp goal' (name ++ altSuff)
      let res ← Simp.mkCongrArg context res
      res.mkEqMPR prf

end VCGen

def elabInvariants (stx : Syntax) (invariants : Array MVarId) (suggestInvariant : MVarId → TacticM Term) : TacticM Unit := do
  let some stx := stx.getOptional? | return ()
  let stx : TSyntax ``invariantAlts := ⟨stx⟩
  withRef stx do
  match stx with
  | `(invariantAlts| $invariantsKW $alts*) =>
    let invariants ← invariants.filterM (not <$> ·.isAssigned)

    let mut dotOrCase := LBool.undef -- .true => dot
    for h : n in 0...alts.size do
      let alt := alts[n]
      match alt with
      | `(invariantDotAlt| · $rhs) =>
        if dotOrCase matches .false then
          logErrorAt alt m!"Alternation between labelled and bulleted invariants is not supported."
          break
        dotOrCase := .true
        let some mv := invariants[n]? | do
          logErrorAt alt m!"More invariants have been defined ({alts.size}) than there were unassigned invariants goals `inv<n>` ({invariants.size})."
          continue
        withRef rhs do
        discard <| evalTacticAt (← `(tactic| exact $rhs)) mv
      | `(invariantCaseAlt| | $tag $args* => $rhs) =>
        if dotOrCase matches .true then
          logErrorAt alt m!"Alternation between labelled and bulleted invariants is not supported."
          break
        dotOrCase := .false
        let n? : Option Nat := do
            let `(binderIdent| $tag:ident) := tag | some n -- fall back to ordinal
            let .str .anonymous s := tag.getId | none
            s.dropPrefix? "inv" >>= String.Slice.toNat?
        let some mv := do invariants[(← n?) - 1]? | do
          logErrorAt alt m!"No invariant with label {tag} {repr tag}."
          continue
        if ← mv.isAssigned then
          logErrorAt alt m!"Invariant {n?.get!} is already assigned."
          continue
        withRef rhs do
        discard <| evalTacticAt (← `(tactic| rename_i $args*; exact $rhs)) mv
      | _ => logErrorAt alt m!"Expected `invariantDotAlt`, got {alt}"

    if let `(invariantsKW| invariants) := invariantsKW then
      if alts.size < invariants.size then
        let missingTypes ← invariants[alts.size:].toArray.mapM (·.getType)
        throwErrorAt stx m!"Lacking definitions for the following invariants.\n{toMessageList missingTypes}"
    else
      -- Otherwise, we have `invariants?`. Suggest missing invariants.
      let mut suggestions := #[]
      for i in 0...invariants.size do
        let mv := invariants[i]!
        if ← mv.isAssigned then
          continue
        let invariant ← suggestInvariant mv
        suggestions := suggestions.push (← `(invariantDotAlt| · $invariant))
      let alts' := alts ++ suggestions
      let stx' ← `(invariantAlts|invariants $alts'*)
      if suggestions.size > 0 then
        Lean.Meta.Tactic.TryThis.addSuggestion stx stx'
      else
        logInfoAt stx m!"There were no suggestions for missing invariants."
  | _ => logErrorAt stx m!"Expected invariantAlts, got {stx}"

def patchVCAltIntoCaseTactic (alt : TSyntax ``vcAlt) : TSyntax ``case :=
  -- syntax vcAlt := sepBy1(caseArg, " | ") " => " tacticSeq
  -- syntax case := "case " sepBy1(caseArg, " | ") " => " tacticSeq
  ⟨alt.raw |>.setKind ``case |>.setArg 0 (mkAtom "case")⟩

public meta partial def elabVCs (stx : Syntax) (vcs : Array MVarId) : TacticM (List MVarId) := do
  let some stx := stx.getOptional? | return vcs.toList
  match (⟨stx⟩ : TSyntax ``vcAlts) with
  | `(vcAlts| with $(tactic)? $alts*) =>
    let vcs ← applyPreTac vcs tactic
    evalAlts vcs alts
  | _ =>
    logErrorAt stx m!"Expected inductionAlts, got {stx}"
    return vcs.toList
where
  applyPreTac (vcs : Array MVarId) (tactic : Option Syntax) : TacticM (Array MVarId) := do
    let some tactic := tactic | return vcs
    let mut newVCs := #[]
    for vc in vcs do
      let vcs ← evalTacticAt tactic vc
      newVCs := newVCs ++ vcs
    return newVCs

  evalAlts (vcs : Array MVarId) (alts : TSyntaxArray ``vcAlt) : TacticM (List MVarId) := do
    let oldGoals ← getGoals
    try
      setGoals vcs.toList
      for alt in alts do withRef alt <| evalTactic <| patchVCAltIntoCaseTactic alt
      pruneSolvedGoals
      getGoals
    finally
      setGoals oldGoals

@[tactic_alt Lean.Parser.Tactic.mvcgenMacro]
syntax (name := mvcgen') "mvcgen'" optConfig
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")?
  (invariantAlts)? (vcAlts)? : tactic

@[tactic mvcgen']
public def elabMVCGen : Tactic := fun stx => withMainContext do
  if mvcgen.warning.get (← getOptions) then
    logWarningAt stx "The `mvcgen` tactic is experimental and still under development. Avoid using it in production projects."
  let ctx ← mkSpecContext stx[1] stx[2]
  let fuel := match ctx.config.stepLimit with
    | some n => .limited n
    | none => .unlimited
  let goal ← getMainGoal
  let goal ← if ctx.config.elimLets then elimLets goal else pure goal
  let { invariants, vcs } ← VCGen.genVCs goal ctx fuel
  trace[Elab.Tactic.Do.vcgen] "after genVCs {← (invariants ++ vcs).mapM fun m => m.getTag}"
  let runOnVCs (tac : TSyntax `tactic) (vcs : Array MVarId) : TermElabM (Array MVarId) :=
    vcs.flatMapM fun vc => List.toArray <$> Term.withSynthesize do
      Tactic.run vc (Tactic.evalTactic tac *> Tactic.pruneSolvedGoals)
  let invariants ← Term.TermElabM.run' do
    let invariants ← if ctx.config.leave then runOnVCs (← `(tactic| try mleave)) invariants else pure invariants
  trace[Elab.Tactic.Do.vcgen] "before elabInvariants {← (invariants ++ vcs).mapM fun m => m.getTag}"
  elabInvariants stx[3] invariants (suggestInvariant vcs)
  let invariants ← invariants.filterM (not <$> ·.isAssigned)
  trace[Elab.Tactic.Do.vcgen] "before trying trivial VCs {← (invariants ++ vcs).mapM fun m => m.getTag}"
  let vcs ← Term.TermElabM.run' do
    let vcs ← if ctx.config.trivial then runOnVCs (← `(tactic| try mvcgen_trivial)) vcs else pure vcs
    let vcs ← if ctx.config.leave then runOnVCs (← `(tactic| try mleave)) vcs else pure vcs
    return vcs
  -- Eliminating lets here causes some metavariables in `mkFreshPair_triple` to become nonassignable
  -- so we don't do it. Presumably some weird delayed assignment thing is going on.
  -- let vcs ← if ctx.config.elimLets then liftMetaM <| vcs.mapM elimLets else pure vcs
  trace[Elab.Tactic.Do.vcgen] "before elabVCs {← (invariants ++ vcs).mapM fun m => m.getTag}"
  let vcs ← elabVCs stx[4] vcs
  trace[Elab.Tactic.Do.vcgen] "before replacing main goal {← (invariants ++ vcs).mapM fun m => m.getTag}"
  replaceMainGoal (invariants ++ vcs).toList
  -- trace[Elab.Tactic.Do.vcgen] "replaced main goal, new: {← getGoals}"

@[builtin_tactic Lean.Parser.Tactic.mvcgenHint]
def elabMVCGenHint : Tactic := fun stx => withMainContext do
  let stx' : TSyntax ``mvcgen := TSyntax.mk <| stx
    |>.setKind ``Lean.Parser.Tactic.mvcgen
    |>.modifyArgs (·.set! 0 (mkAtom "mvcgen") |>.push (mkNullNode #[← `(invariantAlts| invariants?)]) |>.push mkNullNode)
  -- logInfo m!"{stx}\n{toString stx}\n{repr stx}"
  -- logInfo m!"{stx'}\n{toString stx'}\n{repr stx'}"
  Lean.Meta.Tactic.TryThis.addSuggestion stx stx'
