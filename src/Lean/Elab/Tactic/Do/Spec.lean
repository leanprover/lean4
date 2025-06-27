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

def elabTermIntoSpecTheorem (stx : TSyntax `term) (expectedTy : Expr) : TacticM (SpecTheorem × List MVarId) := do
  if stx.raw.isIdent then
    match ← Term.resolveId? stx.raw (withInfo := true) with
    | some (.const declName _) => return (← mkSpecTheoremFromConst declName, [])
    | some (.fvar fvarId) => return (← mkSpecTheoremFromLocal fvarId, [])
    | _      => pure ()
  try
    let (prf, mvars) ← --Term.withSynthesize <|
      elabTermWithHoles stx expectedTy `mspec (allowNaturalHoles := true)
    let specThm ← mkSpecTheoremFromStx stx.raw prf
    return (specThm, mvars)
  catch e : Exception =>
    trace[Elab.Tactic.Do.spec] "Internal error. This happens for example when the head symbol of the spec is wrong. Message:\n  {e.toMessageData}"
    throw e

def elabSpec (stx? : Option (TSyntax `term)) (wp : Expr) : TacticM (SpecTheorem × List MVarId) := do
  let_expr f@WP.wp m ps instWP α prog := wp | throwError "target not a wp application {wp}"
  let P ← mkFreshExprMVar (mkApp (mkConst ``Assertion) ps) (userName := `P)
  let Q ← mkFreshExprMVar (mkApp2 (mkConst ``PostCond) α ps) (userName := `Q)
  let expectedTy := mkApp7 (mkConst ``Triple f.constLevels!) m ps instWP α prog P Q
  trace[Elab.Tactic.Do.spec] "spec syntax: {stx?}"
  trace[Elab.Tactic.Do.spec] "expected type: {← instantiateMVars expectedTy}"
  match stx? with
  | none => pure (← findSpec (← getSpecTheorems) wp, [])
  | some stx => elabTermIntoSpecTheorem stx expectedTy

variable {n} [Monad n] [MonadControlT MetaM n] [MonadLiftT MetaM n]

private def mkProj' (n : Name) (i : Nat) (Q : Expr) : MetaM Expr := do
  return (← projectCore? Q i).getD (mkProj n i Q)

mutual
partial def dischargePostEntails (α : Expr) (ps : Expr) (Q : Expr) (Q' : Expr) (goalTag : Name) (discharge : Expr → Name → n Expr) : n Expr := do
  -- Often, Q' is fully instantiated while Q contains metavariables. Try refl
  if (← isDefEq Q Q') then
    return mkApp3 (mkConst ``PostCond.entails.refl) α ps Q'
  let Q ← whnfR Q
  let Q' ← whnfR Q'
  -- If Q (postcond of the spec) is just an fvar, we do not decompose further
  if let some _fvarId := Q.fvarId? then
    return ← discharge (mkApp4 (mkConst ``PostCond.entails) α ps Q Q') (goalTag ++ `post)
  -- Otherwise decompose the conjunction
  let prf₁ ← withLocalDeclD Name.anonymous α fun a => do
    let Q1a := (← mkProj' ``Prod 0 Q).betaRev #[a]
    let Q'1a := (← mkProj' ``Prod 0 Q').betaRev #[a]
    let σs := mkApp (mkConst ``PostShape.args) ps
    let uniq ← liftMetaM mkFreshId
    let goal := MGoal.mk σs (Hyp.mk `h uniq Q1a).toExpr Q'1a
    mkLambdaFVars #[a] (← discharge goal.toExpr (goalTag ++ `success))
  let prf₂ ← dischargeFailEntails ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q') (goalTag ++ `except) discharge
  mkAppM ``And.intro #[prf₁, prf₂] -- This is just a bit too painful to construct by hand

partial def dischargeFailEntails (ps : Expr) (Q : Expr) (Q' : Expr) (goalTag : Name) (discharge : Expr → Name → n Expr) : n Expr := do
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
    return ← dischargeFailEntails ps Q Q' goalTag discharge
  if let some (ε, ps) := ps.app2? ``PostShape.except then
    let Q ← whnfR Q
    let Q' ← whnfR Q'
    let prf₁ ← withLocalDeclD Name.anonymous ε fun e => do
      let Q1e := (← mkProj' ``Prod 0 Q).betaRev #[e]
      let Q'1e := (← mkProj' ``Prod 0 Q').betaRev #[e]
      let σs := mkApp (mkConst ``PostShape.args) ps
      let uniq ← liftMetaM mkFreshId
      let goal := MGoal.mk σs (Hyp.mk `h uniq Q1e).toExpr Q'1e
      mkLambdaFVars #[e] (← discharge goal.toExpr (goalTag ++ `handle))
    let prf₂ ← dischargeFailEntails ps (← mkProj' ``Prod 1 Q) (← mkProj' ``Prod 1 Q') (goalTag ++ `except) discharge
    return ← mkAppM ``And.intro #[prf₁, prf₂] -- This is just a bit too painful to construct by hand
  -- This case happens when decomposing with unknown `ps : PostShape`
  discharge (mkApp3 (mkConst ``FailConds.entails) ps Q Q') goalTag
end

def dischargeMGoal (goal : MGoal) (goalTag : Name) (discharge : Expr → Name → n Expr) : n Expr := do
  -- controlAt MetaM (fun map => do trace[Elab.Tactic.Do.spec] "dischargeMGoal: {(← reduceProj? goal.target).getD goal.target}"; map (pure ()))
  -- simply try one of the assumptions for now. Later on we might want to decompose conjunctions etc; full xsimpl
  let some prf ← liftMetaM goal.assumption | discharge goal.toExpr goalTag
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
def mSpec (goal : MGoal) (elabSpecAtWP : Expr → n (SpecTheorem × List MVarId)) (discharge : Expr → Name → n Expr) (goalTag : Name) (mkPreTag := mkPreTag) : n (Expr × List MVarId) := do
  -- First instantiate `fun s => ...` in the target via repeated `mintro ∀s`.
  let (holes, prf) ← mIntroForallN goal goal.target.consumeMData.getNumHeadLambdas fun goal => do
    -- Elaborate the spec for the wp⟦e⟧ app in the target
    let T := goal.target.consumeMData
    unless T.getAppFn.constName! == ``PredTrans.apply do
      liftMetaM (throwError "target not a PredTrans.apply application {indentExpr T}")
    let wp := T.getArg! 2
    liftMetaM <| do trace[Elab.Tactic.Do.spec] "before elabSpecAtWP {wp}"
    let (specThm, elabMVars) ← elabSpecAtWP wp
    liftMetaM <| do trace[Elab.Tactic.Do.spec] "after elabSpecAtWP {specThm.proof} {wp}"

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
    let (schematicMVars, _, spec, specTy) ← specThm.proof.instantiate

    -- Apply the spec to the excess arguments of the `wp⟦e⟧ Q` application
    let T := goal.target.consumeMData
    let args := T.getAppArgs
    let Q' := args[3]!
    let excessArgs := (args.extract 4 args.size).reverse

    liftMetaM <| do trace[Elab.Tactic.Do.spec] "before WTF {wp} {spec} {specTy}"
    -- Actually instantiate the specThm using the expected type computed from `wp`.
    let_expr f@Triple m ps instWP α prog P Q := specTy | do liftMetaM (throwError "target not a Triple application {specTy}")
    let wp' := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog
    unless (← withAssignableSyntheticOpaque <| isDefEq wp wp') do
      Term.throwTypeMismatchError none wp wp' spec
    liftMetaM <| do trace[Elab.Tactic.Do.spec] "WTF {wp} {wp'} {spec} {specTy}"

    let P := P.betaRev excessArgs
    let spec := spec.betaRev excessArgs

    -- often P or Q are schematic (i.e. an MVar app). Try to solve by rfl.
    let P ← instantiateMVarsIfMVarApp P
    let Q ← instantiateMVarsIfMVarApp Q
    let HPRfl ← withDefault <| withAssignableSyntheticOpaque <| isDefEqGuarded P goal.hyps
    let QQ'Rfl ← withDefault <| withAssignableSyntheticOpaque <| isDefEqGuarded Q Q'

    -- Discharge the validity proof for the spec if not rfl
    let mut prePrf : Expr → Expr := id
    if !HPRfl then
      -- let P := (← reduceProjBeta? P).getD P
      -- Try to avoid creating a longer name if the postcondition does not need to create a goal
      let tag := if !QQ'Rfl then mkPreTag goalTag else goalTag
      let HPPrf ← dischargeMGoal { goal with target := P } tag discharge
      prePrf := mkApp6 (mkConst ``SPred.entails.trans) goal.σs goal.hyps P goal.target HPPrf

    -- Discharge the entailment on postconditions if not rfl
    let mut postPrf : Expr → Expr := id
    if !QQ'Rfl then
      -- Try to avoid creating a longer name if the precondition does not need to create a goal
      let tag := if !HPRfl then goalTag ++ `post else goalTag
      let wpApplyQ  := mkApp4 (mkConst ``PredTrans.apply) ps α wp Q  -- wp⟦x⟧.apply Q; that is, T without excess args
      let wpApplyQ' := mkApp4 (mkConst ``PredTrans.apply) ps α wp Q' -- wp⟦x⟧.apply Q'
      let QQ' ← dischargePostEntails α ps Q Q' tag discharge
      let QQ'mono := mkApp6 (mkConst ``PredTrans.mono) ps α wp Q Q' QQ'
      postPrf := fun h =>
        mkApp6 (mkConst ``SPred.entails.trans) goal.σs P (wpApplyQ.betaRev excessArgs) (wpApplyQ'.betaRev excessArgs)
          h (QQ'mono.betaRev excessArgs)

    -- finally build the proof; HPPrf.trans (spec.trans QQ'mono)
    let prf := prePrf (postPrf spec)
    let holes := elabMVars ++ schematicMVars.toList.map (·.mvarId!)
    let holes ← liftMetaM <| holes.filterM fun mv => not <$> mv.isAssignedOrDelayedAssigned
    return (holes, prf)

  -- (This is after closing the `mForallIntro` and `mTryFrame` blocks.)
  -- Functions like `mkForallFVars` etc. might have instantiated some of the MVar holes and in
  -- doing so have introduced new MVars in turn.
  -- Thus we try and instantiate all MVars and collect the MVars of the instantiated expressions.
  let holes ← liftMetaM <| holes.flatMapM fun mv => do
    let e ← instantiateMVars (mkMVar mv)
    let mvs ← getMVars e
    let mvs ← mvs.filterM fun mv => not <$> mv.isAssignedOrDelayedAssigned
    return mvs.toList
  return (prf, holes)

private def addMVar (mvars : IO.Ref (List MVarId)) (goal : Expr) (name : Name) : MetaM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar goal (tag := name)
  mvars.modify (m.mvarId! :: ·)
  return m

@[builtin_tactic Lean.Parser.Tactic.mspecNoBind]
def evalMSpecNoBind : Tactic
  | `(tactic| mspec_no_bind $[$spec]?) => do
    let (mvar, goal) ← mStartMVar (← getMainGoal)
    mvar.withContext do
    let goals ← IO.mkRef []
    let (prf, specHoles) ← mSpec goal (elabSpec spec) (fun goal name => liftMetaM (addMVar goals goal name)) (← getMainTag)
    mvar.assign prf
    let goals ← goals.get
    if let [mvar'] := goals then mvar'.setTag (← mvar.getTag)
    replaceMainGoal (goals ++ specHoles)
  | _ => throwUnsupportedSyntax

-- TODO: Define the simp set as a list here and build `simpArgs` syntax from it
macro_rules
  | `(tactic| mspec_no_simp $[$spec]?) =>
    `(tactic| ((try with_reducible mspec_no_bind $(mkIdent ``Std.Do.Spec.bind)); mspec_no_bind $[$spec]?))
  | `(tactic| mspec $[$spec]?)         =>
    `(tactic| mspec_no_simp $[$spec]?; open Std.Do in all_goals ((try simp only [SPred.true_intro_simp, SPred.true_intro_simp_nil, SVal.curry_cons, SVal.uncurry_cons, SVal.getThe_here, SVal.getThe_there]); (try mpure_intro; trivial)))
