/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Elab
public import Lean.Meta
public import Lean.Parser
public import Lean.Expr
public meta import Lean.Elab
public meta import Lean.Meta

open Lean Parser Meta Elab Tactic Sym
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do

-- The following spec is necessary because the VC gen currently has no support for unfolding spec
-- theorems, which is what we usually do for `MonadState.get`.
@[spec]
theorem Spec.MonadState_get_StateT {m ps} [Monad m] [WPMonad m ps] {σ} {Q : PostCond σ (.arg σ ps)} :
    ⦃fun s => Q.fst s s⦄ get (m := StateT σ m) ⦃Q⦄ := by
  simp only [Triple, WP.get_MonadState, WP.get_StateT, SPred.entails.refl]

/-!
Some auxiliary theorems for generating smaller proof terms
-/

namespace TacticHelpers

universe u v
variable {m : Type u → Type v} {ps : PostShape.{u}}

theorem apply0_pre_post {α : Type u} [WP m ps]
    {x : m α}
    {P : Assertion ps} {P' : Assertion ps}
    {Q Q' : PostCond α ps}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P') (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h)
  apply (wp x).mono _ _ hpost

theorem apply0_pre {α : Type u} [WP m ps]
    {x : m α}
    {P : Assertion ps} {P' : Assertion ps}
    {Q : PostCond α ps}
    (h : Triple x P' Q) (hpre : P ⊢ₛ P') : P ⊢ₛ wp⟦x⟧ Q :=
  apply0_pre_post h hpre .rfl

theorem apply1_pre_post {α σ : Type u} [WP m (.arg σ ps)]
    {x : m α} {s : σ}
    {P : Assertion ps} {P' : Assertion (.arg σ ps)}
    {Q Q' : PostCond α (.arg σ ps)}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P' s) (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q s := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h)
  apply (wp x).mono _ _ hpost

theorem apply1_pre {α σ : Type u} [WP m (.arg σ ps)]
    {x : m α} {s : σ}
    {P : Assertion ps} {P' : Assertion (.arg σ ps)}
    {Q : PostCond α (.arg σ ps)}
    (h : Triple x P' Q) (hpre : P ⊢ₛ P' s) : P ⊢ₛ wp⟦x⟧ Q s :=
  apply1_pre_post h hpre .rfl

theorem apply2_pre_post {α σ₁ σ₂ : Type u} [WP m (.arg σ₁ (.arg σ₂ ps))]
    {x : m α} {s₁ : σ₁} {s₂ : σ₂}
    {P : Assertion ps} {P' : Assertion (.arg σ₁ (.arg σ₂ ps))}
    {Q Q' : PostCond α (.arg σ₁ (.arg σ₂ ps))}
    (h : Triple x P' Q') (hpre : P ⊢ₛ P' s₁ s₂) (hpost : Q' ⊢ₚ Q) : P ⊢ₛ wp⟦x⟧ Q s₁ s₂ := by
  apply SPred.entails.trans hpre
  apply SPred.entails.trans (Triple.iff.mp h)
  apply (wp x).mono _ _ hpost

theorem apply2_pre {α σ₁ σ₂ : Type u} [WP m (.arg σ₁ (.arg σ₂ ps))]
    {x : m α} {s₁ : σ₁} {s₂ : σ₂}
    {P : Assertion ps} {P' : Assertion (.arg σ₁ (.arg σ₂ ps))}
    {Q : PostCond α (.arg σ₁ (.arg σ₂ ps))}
    (h : Triple x P' Q) (hpre : P ⊢ₛ P' s₁ s₂) : P ⊢ₛ wp⟦x⟧ Q s₁ s₂ :=
  apply2_pre_post h hpre .rfl

meta def knownApplyTheorems : Std.HashMap (Bool × Bool × Nat) Name := .ofList [
    -- (pre, post, excess args)
    ((true, false, 0), ``apply0_pre),
    ((true, false, 1), ``apply1_pre),
    ((true, false, 2), ``apply2_pre),
    ((true, true, 0), ``apply0_pre_post),
    ((true, true, 1), ``apply1_pre_post),
    ((true, true, 2), ``apply2_pre_post),
  ]

end TacticHelpers

/-!
Creating backward rules for registered specifications
-/

namespace Lean.Elab.Tactic.Do.SpecAttr

meta def SpecTheorems.findSpec (database : SpecTheorems) (e : Expr) : MetaM (Option SpecTheorem) := do
  let candidates ← database.specs.getMatch e
  let candidates := candidates.filter fun spec => !database.erased.contains spec.proof
  let specs := candidates.insertionSort fun s₁ s₂ => s₁.priority > s₂.priority
  return specs[0]?

meta def mkApplyTheorem (pre post : Bool) (us : List Level) (m ps α instWP prog P Q h : Expr) (ss : Array Expr) (ys : Array Expr) : Option Expr := do
  let thm ← TacticHelpers.knownApplyTheorems.get? (pre, post, ss.size)
  let mut σs := #[]
  let mut ps := ps
  for _ in [:ss.size] do
    let (σ, ps') ← ps.app2? ``PostShape.arg
    σs := σs.push σ
    ps := ps'
  let mut prf := mkConst thm us
  prf := mkApp3 prf m ps α
  prf := mkAppN prf σs
  prf := mkApp2 prf instWP prog
  prf := mkAppN prf ss
  if pre then prf := mkApp prf ys[0]! -- P'
  prf := mkApp prf P
  if post then prf := mkApp prf ys[ys.size-2]! -- Q'
  prf := mkApp2 prf Q h
  if pre then prf := mkApp prf ys[1]! -- hpre
  if post then prf := mkApp prf ys[ys.size-1]! -- hpost
  return prf

open TacticHelpers in
meta def SpecTheorem.mkBackwardRuleFromSpec (specThm : SpecTheorem) (m σs ps instWP : Expr) (excessArgs : Array Expr) : SymM BackwardRule := do
  -- Create a backward rule for the spec we look up in the database.
  -- In order for the backward rule to apply, we need to instantiate both `m` and `ps` with the ones
  -- given by the use site.
  let (xs, _bs, spec, specTy) ← specThm.proof.instantiate
  let_expr f@Triple m' ps' instWP' α prog P Q := specTy
    | liftMetaM <| throwError "target not a Triple application {specTy}"
  unless ← isDefEqGuarded m m' do -- TODO: Try isDefEqS?
    Term.throwTypeMismatchError none m m' spec
  unless ← isDefEqGuarded ps ps' do
    Term.throwTypeMismatchError none ps ps' spec
  unless ← isDefEqGuarded instWP instWP' do
    Term.throwTypeMismatchError none instWP instWP' spec

  -- We must ensure that P and Q are pattern variables so that the spec matches for every potential
  -- P and Q. We do so by introducing VCs accordingly.
  -- The following code could potentially be extracted into a definition at @[spec] attribute
  -- annotation time. That might help a bit with kernel checking time.
  let excessArgNamesTypes ← excessArgs.mapM fun arg =>
    return (← mkFreshUserName `s, ← Sym.inferType arg)
  let spec ← withLocalDeclsDND excessArgNamesTypes fun ss => do
    let needPreVC := !xs.contains P
    let needPostVC := !xs.contains Q
    let us := f.constLevels!
    let u := us[0]!
    let wp := mkApp5 (mkConst ``WP.wp us) m ps instWP α prog
    let wpApplyQ := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q  -- wp⟦prog⟧ Q
    let Pss := mkAppN P ss  -- P s₁ ... sₙ
    let typeP := mkApp (mkConst ``SPred [u]) σs
      -- Note that this is the type of `P s₁ ... sₙ`,
      -- which is `Assertion ps'`, but we don't know `ps'`
    let typeQ := mkApp2 (mkConst ``PostCond [u]) α ps
    let mut declInfos := #[]
    if needPreVC then
      let nmP' ← mkFreshUserName `P
      let nmHPre ← mkFreshUserName `hpre
      let entailment P' := pure <| mkApp3 (mkConst ``SPred.entails [u]) σs P' Pss
      declInfos := #[(nmP', .strictImplicit, fun _ => pure typeP),
                     (nmHPre, .default, fun xs => entailment xs[0]!)]
    if needPostVC then
      let nmQ' ← mkFreshUserName `Q
      let nmHPost ← mkFreshUserName `hpost
      let entailment Q' := pure <| mkApp3 (mkConst ``PostCond.entails [u]) ps Q Q'
      declInfos := declInfos ++
                   #[(nmQ', .strictImplicit, fun _ => pure typeQ),
                     (nmHPost, .default, fun xs => entailment xs[0]!)]
    withLocalDecls declInfos fun ys => liftMetaM ∘ mkLambdaFVars (ss ++ ys) =<< do
      if !needPreVC && !needPostVC && excessArgs.isEmpty then
        -- Still need to unfold the triple in the spec type
        let entailment := mkApp3 (mkConst ``SPred.entails [u]) σs P wpApplyQ
        let prf := mkApp2 (mkConst ``id [0]) entailment spec
        -- check prf
        return prf
      -- Sadly, the following does not yield a kernel checking speedup (on the contrary), so it's pointless:
      -- if let some prf := mkApplyTheorem needPreVC needPostVC us m ps α instWP prog P Q spec ss ys then
      --   -- check prf
      --   return prf
      let mut prf := spec
      let P := Pss  -- P s₁ ... sₙ
      let wpApplyQ := mkAppN wpApplyQ ss  -- wp⟦prog⟧ Q s₁ ... sₙ
      prf := mkAppN prf ss -- Turn `⦃P⦄ prog ⦃Q⦄` into `P s₁ ... sₙ ⊢ₛ wp⟦prog⟧ Q s₁ ... sₙ`
      let mut newP := P
      let mut newQ := Q
      if needPreVC then
        -- prf := hpre.trans prf
        let P' := ys[0]!
        let hpre := ys[1]!
        prf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs P' P wpApplyQ hpre prf
        newP := P'
        -- check prf
      if needPostVC then
        -- prf := prf.trans <| (wp x).mono _ _ hpost
        let wp := mkApp5 (mkConst ``WP.wp f.constLevels!) m ps instWP α prog
        let Q' := ys[ys.size-2]!
        let hpost := ys[ys.size-1]!
        let wpApplyQ' := mkApp4 (mkConst ``PredTrans.apply [u]) ps α wp Q' -- wp⟦prog⟧ Q'
        let wpApplyQ' := mkAppN wpApplyQ' ss -- wp⟦prog⟧ Q' s₁ ... sₙ
        let hmono := mkApp6 (mkConst ``PredTrans.mono [u]) ps α wp Q Q' hpost
        let hmono := mkAppN hmono ss
        prf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs newP wpApplyQ wpApplyQ' prf hmono
        newQ := Q'
        -- check prf
      return prf
  let res ← abstractMVars spec
  mkBackwardRuleFromExpr res.expr res.paramNames.toList

end Lean.Elab.Tactic.Do.SpecAttr

/-!
VC generation
-/

public structure VCGen.Context where
  specThms : SpecTheorems
  /-- The backward rule for `SPred.entails_cons_intro`. -/
  entailsConsIntroRule : BackwardRule

public structure VCGen.State where
  /--
  A cache mapping registered SpecThms to their backward rule to apply.
  The particular rule depends on the theorem name, the monad and the number of excess state
  arguments that the weakest precondition target is applied to.
  -/
  specBackwardRuleCache : Std.HashMap (Name × Expr × Nat) BackwardRule := {}
  /--
  Holes of type `Invariant` that have been generated so far.
  -/
  invariants : Array MVarId := #[]
  /--
  The verification conditions that have been generated so far.
  -/
  vcs : Array MVarId := #[]

abbrev VCGenM := ReaderT VCGen.Context (StateRefT VCGen.State SymM)

namespace VCGen

meta def mkBackwardRuleFromSpecCached (specThm : SpecTheorem) (m σs ps instWP : Expr) (excessArgs : Array Expr) : VCGenM BackwardRule := do
  let mkRuleSlow := specThm.mkBackwardRuleFromSpec m σs ps instWP excessArgs
  let s ← get
  let .global decl := specThm.proof | mkRuleSlow
  let key := (decl, m, excessArgs.size)
  if let some p := s.specBackwardRuleCache.get? key then
    return p
  let rule ← mkRuleSlow
  set { s with specBackwardRuleCache := s.specBackwardRuleCache.insert key rule }
  return rule

meta def unfoldTriple (goal : MVarId) : SymM MVarId := goal.withContext do
  let type ← goal.getType
  unless type.isAppOf ``Triple do return goal
  let type ← unfoldDefinition type
  let goal' ← mkFreshExprSyntheticOpaqueMVar type
  goal.assign goal'
  preprocessMVar goal'.mvarId!  -- need to reinstate subterm sharing. TODO: replace `unfoldDefinition`

open Lean.Elab.Tactic.Do in
meta def simplifyTarget (goal : MVarId) : _root_.VCGenM MVarId := goal.withContext do
  let target ← goal.getType
  let_expr ent@SPred.entails σs P T := target | return goal
  let some T ← reduceProjBeta? T | return goal -- very slight simplification
  let goal' ← mkFreshExprSyntheticOpaqueMVar (mkApp3 ent σs P T)
  goal.assign goal'
  -- Experiments suggest that `reduceProjBeta?` maintains subterm sharing so we don't need to
  -- `preprocessMVar goal'.mvarId!` here
  return goal'.mvarId!

meta def preprocessGoal (goal : MVarId) : VCGenM (Option MVarId) := do
  let mut goal := goal
  if (← goal.getType).isForall then
    let IntrosResult.goal _ goal' ← Sym.intros goal | failure
    goal := goal'
  goal ← unfoldTriple goal
  goal ← simplifyTarget goal
  return goal

inductive SolveResult where
  /-- `target` was not of the form `H ⊢ₛ T`. -/
  | noEntailment (target : Expr)
  /-- The `T` in `H ⊢ₛ T` was not of the form `wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noProgramFoundInTarget (T : Expr)
  /-- Don't know how to handle `e` in `H ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noStrategyForProgram (e : Expr)
  /-- Did not find a spec for the `e` in `H ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noSpecFoundForProgram (e : Expr)
  /-- Successfully discharged the goal. These are the subgoals. -/
  | goals (subgoals : List MVarId)

meta def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let target ← goal.getType
  trace[Elab.Tactic.Do.vcgen] "target: {target}"
  let_expr SPred.entails σs _H T := target | return .noEntailment target
  -- The goal is of the form `H ⊢ₛ T`. Look for program syntax in `T`.

  if T.isLambda then
    -- This happens after applying the `get` spec. We have `T = fun s => wp⟦.. s⟧ Q s`.
    -- Do what `mIntroForall` does, that is, eta-expand. Note that this introduces an
    -- excess state arg `s`.
    let .goals goals ← (← read).entailsConsIntroRule.apply goal
      | throwError "Applying {.ofConstName ``SPred.entails_cons_intro} to {target} failed. It should not."
    return .goals goals

  let f := T.getAppFn
  unless f.isConstOf ``PredTrans.apply do return .noProgramFoundInTarget T
  let args := T.getAppArgs
  let wp := args[2]!
  let_expr WP.wp m ps instWP _α e := wp | failure
  -- `T` is of the form `wp⟦e⟧ Q s₁ ... sₙ`, where `e` is the program.
  -- We call `s₁ ... sₙ` the excess state args; the backward rules need to account for these.
  -- Excess state args are introduced by the spec of `get` (see lambda case above).
  let excessArgs := args.drop 4
  let e := e.headBeta -- better do this work just once
  withTraceNode `Elab.Tactic.Do.vcgen (msg := fun _ => return m!"Program: {e}") do

  -- Apply registered specifications.
  if f.isConst || f.isFVar then
    trace[Elab.Tactic.Do.vcgen] "Applying a spec for {e}. Excess args: {excessArgs}"
    let some thm ← (← read).specThms.findSpec e
      | return .noSpecFoundForProgram e
    let rule ← mkBackwardRuleFromSpecCached thm m σs ps instWP excessArgs
    let ApplyResult.goals goals ← rule.apply goal
      | throwError "Failed to apply rule {thm.proof} for {e}"
    return .goals goals

  return .noStrategyForProgram e

meta def emitVC (goal : MVarId) : VCGenM Unit := do
  let ty ← goal.getType
  goal.setKind .syntheticOpaque
  if ty.isAppOf ``Std.Do.Invariant then
    modify fun s => { s with invariants := s.invariants.push goal }
  else
    modify fun s => { s with vcs := s.vcs.push goal }

meta def work (goal : MVarId) : VCGenM Unit := do
  let mut worklist := Std.Queue.empty.enqueue (← preprocessMVar goal)
  -- while let some (goal, worklist') := worklist.dequeue? do
  repeat do
    let some (goal, worklist') := worklist.dequeue? | break
    worklist := worklist'
    let some goal ← preprocessGoal goal | continue
    -- let goal ← preprocessMVar goal
    let res ← solve goal
    match res with
    | .noEntailment .. | .noProgramFoundInTarget .. =>
      emitVC goal
    | .noSpecFoundForProgram prog =>
      throwError "No spec found for program {prog}"
    | .noStrategyForProgram prog =>
      throwError "Did not know how to decompose weakest precondition for {prog}"
    | .goals subgoals =>
      worklist := worklist.enqueueAll subgoals

public structure Result where
  invariants : Array MVarId
  vcs : Array MVarId

public meta partial def main (goal : MVarId) (ctx : Context) : SymM Result := do
  let ((), state) ← StateRefT'.run (ReaderT.run (work goal) ctx) {}
  for h : idx in [:state.invariants.size] do
    let mv := state.invariants[idx]
    mv.setTag (Name.mkSimple ("inv" ++ toString (idx + 1)))
  for h : idx in [:state.vcs.size] do
    let mv := state.vcs[idx]
    mv.setTag (Name.mkSimple ("vc" ++ toString (idx + 1)) ++ (← mv.getTag).eraseMacroScopes)
  return { invariants := state.invariants, vcs := state.vcs }

/-- This function is best ignored; it's copied from `Lean.Elab.Tactic.Do.mkSpecContext`. -/
meta def mkSpecContext (lemmas : Syntax) (ignoreStarArg := false) : TacticM VCGen.Context := do
  let mut specThms ← getSpecTheorems
  let mut simpStuff := #[]
  let mut starArg := false
  for arg in lemmas[1].getSepArgs do
    if arg.getKind == ``simpErase then
      try
        -- Try and build SpecTheorems for the lemma to erase to see if it's
        -- meant to be interpreted by SpecTheorems. Otherwise fall back to SimpTheorems.
        let specThm ←
          if let some fvar ← Term.isLocalIdent? arg[1] then
            mkSpecTheoremFromLocal fvar.fvarId!
          else
            let id := arg[1]
            if let .ok declName ← observing (realizeGlobalConstNoOverloadWithInfo id) then
              mkSpecTheoremFromConst declName
            else
              withRef id <| throwUnknownConstant id.getId.eraseMacroScopes
        specThms := specThms.eraseCore specThm.proof
      catch _ =>
        simpStuff := simpStuff.push ⟨arg⟩ -- simp tracks its own erase stuff
    else if arg.getKind == ``simpLemma then
      unless arg[0].isNone && arg[1].isNone do
        -- When there is ←, →, ↑ or ↓ then this is for simp
        simpStuff := simpStuff.push ⟨arg⟩
        continue
      let term := arg[2]
      match ← Term.resolveId? term (withInfo := true) <|> Term.elabCDotFunctionAlias? ⟨term⟩ with
      | some (.const declName _) =>
        let info ← getConstInfo declName
        try
          let thm ← mkSpecTheoremFromConst declName
          specThms := addSpecTheoremEntry specThms thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | some (.fvar fvar) =>
        let decl ← getFVarLocalDecl (.fvar fvar)
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := addSpecTheoremEntry specThms thm
        catch _ =>
          simpStuff := simpStuff.push ⟨arg⟩
      | _ => withRef term <| throwError "Could not resolve {repr term}"
    else if arg.getKind == ``simpStar then
      starArg := true
      simpStuff := simpStuff.push ⟨arg⟩
    else
      throwUnsupportedSyntax
  -- Build a mock simp call to build a simp context that corresponds to `simp [simpStuff]`
  let stx ← `(tactic| simp +unfoldPartialApp -zeta [$(Syntax.TSepArray.ofElems simpStuff),*])
  -- logInfo s!"{stx}"
  let res ← mkSimpContext stx.raw
    (eraseLocal := false)
    (simpTheorems := getSpecSimpTheorems)
    (ignoreStarArg := ignoreStarArg)
  -- trace[Elab.Tactic.Do.vcgen] "{res.ctx.simpTheorems.map (·.toUnfold.toList)}"
  if starArg && !ignoreStarArg then
    let fvars ← getPropHyps
    for fvar in fvars do
      unless specThms.isErased (.local fvar) do
        try
          let thm ← mkSpecTheoremFromLocal fvar
          specThms := addSpecTheoremEntry specThms thm
        catch _ => continue
  let entailsConsIntroRule ← mkBackwardRuleFromDecl ``SPred.entails_cons_intro
  return { specThms, entailsConsIntroRule }

end VCGen

syntax (name := mvcgen') "mvcgen'"
  (" [" withoutPosition((simpStar <|> simpErase <|> simpLemma),*,?) "] ")? : tactic

@[tactic mvcgen']
public meta def elabMVCGen' : Tactic := fun stx => withMainContext do
  let ctx ← VCGen.mkSpecContext stx[1]
  let goal ← getMainGoal
  let { invariants, vcs } ← SymM.run <| VCGen.main goal ctx
  replaceMainGoal (invariants ++ vcs).toList

/-!
Local tests for faster iteration:
-/

/-
example : ⦃⌜True⌝⦄ (pure (f := StateM Nat) false) ⦃⇓_ => ⌜True⌝⦄ := by
  set_option trace.Elab.Tactic.Do.spec true in
  set_option trace.Elab.Tactic.Do.vcgen true in
  --set_option pp.all true in
  mvcgen'
  grind

example : ⦃⌜True⌝⦄ (get (m := StateM Nat) >>= set) ⦃⇓_ => ⌜True⌝⦄ := by
  set_option trace.Elab.Tactic.Do.spec true in
  set_option trace.Elab.Tactic.Do.vcgen true in
  --set_option pp.all true in
  mvcgen'
  grind

example :
  ⦃post⦄
  do
    let s ← get (m := StateM Nat)
    set (s + v)
    let s ← get
    set (s - v)
  ⦃⇓_ => post⦄ := by
  mvcgen'
  grind
-/

def step (v : Nat) : StateM Nat Unit := do
  let s ← get
  set (s + v)
  let s ← get
  set (s - v)

def loop (n : Nat) : StateM Nat Unit := do
  match n with
  | 0 => pure ()
  | n+1 => step n; loop n

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

example : ∀ post, ⦃post⦄ loop 100 ⦃⇓_ => post⦄ := by
  intro post
  simp only [loop, step]
  mvcgen'
  sorry
