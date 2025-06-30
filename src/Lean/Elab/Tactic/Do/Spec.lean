/-
Copyright (c) 2022 Lars König. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lars König, Mario Carneiro, Sebastian Graf
-/
prelude
import Lean.Elab.Tactic.Do.ProofMode.Basic
import Lean.Elab.Tactic.Do.ProofMode.Intro
import Lean.Elab.Tactic.Do.ProofMode.Pure
import Lean.Elab.Tactic.Do.ProofMode.Frame
import Lean.Elab.Tactic.Do.ProofMode.Assumption
import Lean.Elab.Tactic.Do.Attr
import Std.Do.Triple

namespace Lean.Elab.Tactic.Do
open Lean Elab Tactic Meta
open Std.Do Do.SpecAttr Do.ProofMode

builtin_initialize registerTraceClass `Elab.Tactic.Do.spec

def findSpec (database : SpecTheorems) (wp : Expr) : MetaM SpecTheorem := do
  let_expr WP.wp _m _ps _instWP _α prog := wp | throwError "target not a wp application {wp}"
  let prog ← instantiateMVarsIfMVarApp prog
  let prog := prog.headBeta
  let candidates ← database.specs.getMatch prog
  let candidates := candidates.filter fun spec => !database.erased.contains spec.proof
  let candidates := candidates.insertionSort fun s₁ s₂ => s₁.priority < s₂.priority
  trace[Elab.Tactic.Do.spec] "Candidates for {prog}: {candidates.map (·.proof)}"
  let specs ← candidates.filterM fun spec => do
    let (_, _, _, type) ← spec.proof.instantiate
    trace[Elab.Tactic.Do.spec] "{spec.proof} instantiates to {type}"
    let_expr Triple m ps instWP α specProg _P _Q := type | throwError "Not a triple: {type}"
    isDefEq wp (mkApp5 (← mkConstWithFreshMVarLevels ``WP.wp) m ps instWP α specProg)
  trace[Elab.Tactic.Do.spec] "Specs for {prog}: {specs.map (·.proof)}"
  if specs.isEmpty then throwError m!"No specs found for {indentExpr prog}\nCandidates: {candidates.map (·.proof)}"
  return specs[0]!

def elabTermIntoSpecTheorem (stx : TSyntax `term) (expectedTy : Expr) : TacticM SpecTheorem := do
  if stx.raw.isIdent then
    match ← Term.resolveId? stx.raw (withInfo := true) with
    | some (.const declName _) => mkSpecTheoremFromConst declName
    | some (.fvar fvarId) => mkSpecTheoremFromLocal fvarId
    | _      => throwError "invalid spec"
  else try
    let (prf, _mvars) ← elabTermWithHoles stx expectedTy `mspec (allowNaturalHoles := true)
    mkSpecTheoremFromStx stx.raw prf
  catch e : Exception =>
    trace[Elab.Tactic.Do.spec] "Internal error. This happens for example when the head symbol of the spec is wrong. Message:\n  {e.toMessageData}"
    throw e

def elabSpec (stx? : Option (TSyntax `term)) (wp : Expr) : TacticM SpecTheorem := do
  let_expr f@WP.wp m ps instWP α prog := wp | throwError "target not a wp application {wp}"
  let P ← mkFreshExprMVar (mkApp (mkConst ``Assertion) ps) (userName := `P)
  let Q ← mkFreshExprMVar (mkApp2 (mkConst ``PostCond) α ps) (userName := `Q)
  let expectedTy := mkApp7 (mkConst ``Triple f.constLevels!) m ps instWP α prog P Q
  trace[Elab.Tactic.Do.spec] "spec syntax: {stx?}"
  trace[Elab.Tactic.Do.spec] "expected type: {← instantiateMVars expectedTy}"
  match stx? with
  | none => findSpec (← getSpecTheorems) wp
  | some stx => elabTermIntoSpecTheorem stx expectedTy

variable {n} [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]

private def mkProj' (n : Name) (i : Nat) (Q : Expr) : MetaM Expr := do
  return (← projectCore? Q i).getD (mkProj n i Q)

mutual
partial def dischargePostEntails (α : Expr) (ps : Expr) (Q : Expr) (Q' : Expr) (goalTag : Name) : n Expr := do
  -- Often, Q' is fully instantiated while Q contains metavariables. Try refl
  if (← isDefEq Q Q') then
    return mkApp3 (mkConst ``PostCond.entails.refl) α ps Q'
  let Q ← whnfR Q
  let Q' ← whnfR Q'
  -- If Q (postcond of the spec) is just an fvar, we do not decompose further
  if let some _fvarId := Q.fvarId? then
    return ← mkFreshExprSyntheticOpaqueMVar (mkApp4 (mkConst ``PostCond.entails) α ps Q Q') (goalTag ++ `post)
  -- Otherwise decompose the conjunction
  let prf₁ ← withLocalDeclD (← liftMetaM <| mkFreshUserName `r) α fun a => do
    let Q1a := (← mkProj' ``Prod 0 Q).betaRev #[a]
    let Q'1a := (← mkProj' ``Prod 0 Q').betaRev #[a]
    let σs := mkApp (mkConst ``PostShape.args) ps
    let uniq ← liftMetaM mkFreshId
    let goal := MGoal.mk σs (Hyp.mk `h uniq Q1a).toExpr Q'1a
    mkLambdaFVars #[a] (← mkFreshExprSyntheticOpaqueMVar goal.toExpr (goalTag ++ `success))
  let prf₂ ← dischargeFailEntails ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q') (goalTag ++ `except)
  mkAppM ``And.intro #[prf₁, prf₂] -- This is just a bit too painful to construct by hand

partial def dischargeFailEntails (ps : Expr) (Q : Expr) (Q' : Expr) (goalTag : Name) : n Expr := do
  if ps.isAppOf ``PostShape.pure then
    return mkConst ``True.intro
  if ← isDefEq Q Q' then
    return mkApp2 (mkConst ``FailConds.entails.refl) ps Q
  if ← isDefEq Q (mkApp (mkConst ``FailConds.false) ps) then
    return mkApp2 (mkConst ``FailConds.entails_false) ps Q'
  if ← isDefEq Q' (mkApp (mkConst ``FailConds.true) ps) then
    return mkApp2 (mkConst ``FailConds.entails_true) ps Q
  -- the remaining cases are recursive.
  if let some (_σ, ps) := ps.app2? ``PostShape.arg then
    return ← dischargeFailEntails ps Q Q' goalTag
  if let some (ε, ps) := ps.app2? ``PostShape.except then
    let Q ← whnfR Q
    let Q' ← whnfR Q'
    let prf₁ ← withLocalDeclD (← liftMetaM <| mkFreshUserName `e) ε fun e => do
      let Q1e := (← mkProj' ``Prod 0 Q).betaRev #[e]
      let Q'1e := (← mkProj' ``Prod 0 Q').betaRev #[e]
      let σs := mkApp (mkConst ``PostShape.args) ps
      let uniq ← liftMetaM mkFreshId
      let goal := MGoal.mk σs (Hyp.mk `h uniq Q1e).toExpr Q'1e
      mkLambdaFVars #[e] (← mkFreshExprSyntheticOpaqueMVar goal.toExpr (goalTag ++ `handle))
    let prf₂ ← dischargeFailEntails ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q') (goalTag ++ `except)
    return ← mkAppM ``And.intro #[prf₁, prf₂] -- This is just a bit too painful to construct by hand
  -- This case happens when decomposing with unknown `ps : PostShape`
  mkFreshExprSyntheticOpaqueMVar (mkApp3 (mkConst ``FailConds.entails) ps Q Q') goalTag
end

def dischargeMGoal (goal : MGoal) (goalTag : Name) : n Expr := do
  liftMetaM <| do trace[Elab.Tactic.Do.spec] "dischargeMGoal: {(← reduceProj? goal.target).getD goal.target}"
  -- simply try one of the assumptions for now. Later on we might want to decompose conjunctions etc; full xsimpl
  -- The `withDefault` ensures that a hyp `⌜s = 4⌝` can be used to discharge `⌜s = 4⌝ s`.
  -- (Recall that `⌜s = 4⌝ s` is `SVal.curry (σs:=[Nat]) (fun _ => s = 4) s` and `SVal.curry` is
  -- semi-reducible.)
  let some prf ← liftMetaM goal.assumption | mkFreshExprSyntheticOpaqueMVar goal.toExpr goalTag
  return prf

def mkPreTag (goalTag : Name) : Name := Id.run do
  let dflt := goalTag ++ `pre1
  let .str p s := goalTag | return dflt
  unless "pre".isPrefixOf s do return dflt
  let some n := (s.toSubstring.drop 3).toString.toNat? | return dflt
  return .str p ("pre" ++ toString (n + 1))

/--
  Returns the proof and the list of new unassigned MVars.
-/
def mSpec (goal : MGoal) (elabSpecAtWP : Expr → n SpecTheorem) (goalTag : Name) (mkPreTag := mkPreTag) : n (Expr × List MVarId) := do
  let mvarCounterSaved := (← liftMetaM getMCtx).mvarCounter
  -- First instantiate `fun s => ...` in the target via repeated `mintro ∀s`.
  let (_, prf) ← mIntroForallN goal goal.target.consumeMData.getNumHeadLambdas fun goal => do
    -- Elaborate the spec for the wp⟦e⟧ app in the target
    let T := goal.target.consumeMData
    unless T.getAppFn.constName! == ``PredTrans.apply do
      liftMetaM (throwError "target not a PredTrans.apply application {indentExpr T}")
    let wp := T.getArg! 2
    let specThm ← elabSpecAtWP wp

    -- The precondition of `specThm` might look like `⌜?n = ‹Nat›ₛ ∧ ?m = ‹Bool›ₛ⌝`, which expands to
    -- `SVal.curry (fun tuple => ?n = SVal.uncurry (getThe Nat tuple) ∧ ?m = SVal.uncurry (getThe Bool tuple))`.
    -- Note that the assignments for `?n` and `?m` depend on the bound variable `tuple`.
    -- Here, we further eta expand and simplify according to `etaPotential` so that the solutions for
    -- `?n` and `?m` do not depend on `tuple`.
    let residualEta := specThm.etaPotential - (T.getAppNumArgs - 4) -- 4 arguments expected for PredTrans.apply
    mIntroForallN goal residualEta fun goal => do

    -- Compute a frame of `P` that we duplicate into the pure context using `Spec.frame`
    -- For now, frame = `P` or nothing at all
    mTryFrame goal fun goal => do

    -- Fully instantiate the specThm without instantiating its MVars to `wp` yet
    let (_, _, spec, specTy) ← specThm.proof.instantiate

    -- Apply the spec to the excess arguments of the `wp⟦e⟧ Q` application
    let T := goal.target.consumeMData
    let args := T.getAppArgs
    let Q' := args[3]!
    let excessArgs := (args.extract 4 args.size).reverse

    -- Actually instantiate the specThm using the expected type computed from `wp`.
    let_expr f@Triple m ps instWP α prog P Q := specTy | do liftMetaM (throwError "target not a Triple application {specTy}")
    let wp' := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog
    unless (← withAssignableSyntheticOpaque <| isDefEq wp wp') do
      Term.throwTypeMismatchError none wp wp' spec

    let P ← instantiateMVarsIfMVarApp P
    let Q ← instantiateMVarsIfMVarApp Q

    let P := P.betaRev excessArgs
    let spec := spec.betaRev excessArgs

    -- Often P or Q are schematic (i.e. an MVar app). Try to solve by rfl.
    -- We do `fullApproxDefEq` here so that `constApprox` is active; this is useful in
    -- `need_const_approx` of `doLogicTests.lean`.
    let (HPRfl, QQ'Rfl) ← withAssignableSyntheticOpaque <| fullApproxDefEq <| do
      return (← isDefEqGuarded P goal.hyps, ← isDefEqGuarded Q Q')

    -- Discharge the validity proof for the spec if not rfl
    let mut prePrf : Expr → Expr := id
    if !HPRfl then
      -- let P := (← reduceProjBeta? P).getD P
      -- Try to avoid creating a longer name if the postcondition does not need to create a goal
      let tag := if !QQ'Rfl then mkPreTag goalTag else goalTag
      let HPPrf ← dischargeMGoal { goal with target := P } tag
      prePrf := mkApp6 (mkConst ``SPred.entails.trans) goal.σs goal.hyps P goal.target HPPrf

    -- Discharge the entailment on postconditions if not rfl
    let mut postPrf : Expr → Expr := id
    if !QQ'Rfl then
      -- Try to avoid creating a longer name if the precondition does not need to create a goal
      let tag := if !HPRfl then goalTag ++ `post else goalTag
      let wpApplyQ  := mkApp4 (mkConst ``PredTrans.apply) ps α wp Q  -- wp⟦x⟧.apply Q; that is, T without excess args
      let wpApplyQ' := mkApp4 (mkConst ``PredTrans.apply) ps α wp Q' -- wp⟦x⟧.apply Q'
      let QQ' ← dischargePostEntails α ps Q Q' tag
      let QQ'mono := mkApp6 (mkConst ``PredTrans.mono) ps α wp Q Q' QQ'
      postPrf := fun h =>
        mkApp6 (mkConst ``SPred.entails.trans) goal.σs P (wpApplyQ.betaRev excessArgs) (wpApplyQ'.betaRev excessArgs)
          h (QQ'mono.betaRev excessArgs)

    -- finally build the proof; HPPrf.trans (spec.trans QQ'mono)
    let prf := prePrf (postPrf spec)
    return ((), prf)

  -- (This is after closing the `mForallIntro` and `mTryFrame` blocks.)
  -- Functions like `mkForallFVars` etc. might have instantiated some of the MVar holes and in
  -- doing so have introduced new MVars in turn.
  -- Thus we try and instantiate all MVars and collect the MVars of the instantiated expressions.
  let holes ← getMVarsNoDelayed prf
  /- Filter out all mvars that were created prior to `k`. -/
  let holes ← filterOldMVars holes mvarCounterSaved
  let holes ← liftMetaM <| sortMVarIdsByIndex holes.toList
  return (prf, holes)

private def addMVar (mvars : IO.Ref (List MVarId)) (goal : Expr) (name : Name) : MetaM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar goal (tag := name)
  mvars.modify (m.mvarId! :: ·)
  return m

@[builtin_tactic Lean.Parser.Tactic.mspecNoBind]
def elabMSpecNoBind : Tactic
  | `(tactic| mspec_no_bind $[$spec]?) => do
    let (mvar, goal) ← mStartMVar (← getMainGoal)
    mvar.withContext do
    let (prf, goals) ← mSpec goal (elabSpec spec) (← getMainTag)
    mvar.assign prf
    replaceMainGoal goals
  | _ => throwUnsupportedSyntax
