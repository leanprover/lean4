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
Creating backward rules for registered specifications
-/

namespace Lean.Elab.Tactic.Do.SpecAttr

def nilEntails.{u} (P Q : ULift.{u, 0} Prop) :=
  SPred.entails (σs := []) P Q

meta def unfoldSPredEntails (e : Expr) : SymM Expr := do
  let pre (e : Expr) : SymM TransformStep := do
    if ← isProp e then
      return .continue e
    else
      return .done e
  let post (e : Expr) : SymM TransformStep := do
    let f := e.getAppFn
    unless f.isConstOf ``SPred.entails do return .done e
    let args := e.getAppArgs
    unless args.size >= 3 do return .done e
    let mut σs := args[0]!
    let mut stateTypes := #[]
    while σs.isAppOfArity ``List.cons 3 do
      stateTypes := stateTypes.push (σs.getArg! 1)
      σs := σs.getArg! 2
    let canUnfoldCompletely := σs.isAppOf ``List.nil
    unless canUnfoldCompletely || stateTypes.size > 0 do return .done e
    let mut res :=
      let ss := (*...stateTypes.size).toArray.reverse.map mkBVar -- [#3, #2, #1, #0]
      let P := mkAppN args[1]! ss
      let Q := mkAppN args[2]! ss
      if canUnfoldCompletely then
        mkApp2 (mkConst ``nilEntails f.constLevels!) P Q
      else
        mkApp3 (mkConst ``SPred.entails f.constLevels!) σs P Q
    for σ in stateTypes.reverse do
      res := mkForall (← mkFreshUserName `s) .default σ res
    res := mkAppN res args[3...*]
    return .done res
  Meta.transform e (pre := pre) (post := post) (skipConstInApp := true)

structure SpecializedWPApplyApp where
  name : Name
  m : Expr
  ps : Expr
  instWP : Expr
  α : Expr
  e : Expr
  Q : Expr
  excessArgs : Array Expr

meta def mkSpecializedWPApply (wp : Expr) (wpRevArgs : Array Expr) : SymM Name := do
  -- Example of produced definition:
  -- def wpApplyStateM (α : Type) (x : StateM Nat α) (Q : (α → Nat → ULift Prop) × ExceptConds (.arg Nat .pure)) : Nat → ULift Prop :=
  --   (wp x).apply Q
  -- where
  --   PredTrans.apply : {ps : PostShape} → {α : Type u} → PredTrans ps α → PostCond α ps → Assertion ps
  --   WP.wp : {m : Type u → Type v} → {ps : outParam PostShape} → [self : WP m ps] → {α : Type u} → m α → PredTrans ps α
  let m := wpRevArgs[4]!
  let ps := wpRevArgs[3]!
  let α := wpRevArgs[1]!
  let _x := wpRevArgs[0]!
  let u := wp.constLevels![0]!
  let e ←
    withLocalDeclD `α (← Sym.inferType α) fun α => do
    withLocalDeclD `x (mkApp m α) fun x => do
    let wpRevArgs := wpRevArgs |>.set! 0 x |>.set! 1 α
    let wpApp := mkAppRev wp wpRevArgs
    let applyApp := mkApp3 (mkConst ``PredTrans.apply [u]) ps α wpApp  -- NB: undersaturated, because we need to unfold in the type of `Q` anyway
    mkLambdaFVars #[α, x] applyApp
  let e ← unfoldReducible e
  let e ← shareCommon e
  let type ← Sym.inferType e
  let type ← unfoldReducible type
  let type ← shareCommon type
  trace[Elab.Tactic.Do.vcgen] "specialized `(wp _).apply` result type: {type}"
  let name ← mkFreshUserName `PredTrans.specializedApply
  -- e is closed, so `_defn` is always `mkConst name`.
  -- This will change once we support polymorphic monads.
  let _defn ← mkAuxDefinition name type e (compile := false)
  enableRealizationsForConst name
  return name

meta def SpecializedWPApplyApp.unfold (app : SpecializedWPApplyApp) : MetaM Expr := do
  let u ← getLevel app.α
  let v ← getLevel (mkApp app.m app.α)
  let wp := mkApp5 (mkConst ``WP.wp [u, v]) app.m app.ps app.instWP app.α app.e
  let apply := mkApp3 (mkConst ``PredTrans.apply [u]) app.ps app.α wp
  return mkAppN apply app.excessArgs

meta def SpecTheorems.findSpec (database : SpecTheorems) (e : Expr) : MetaM (Option SpecTheorem) := do
  let candidates ← database.specs.getMatch e
  let candidates := candidates.filter fun spec => !database.erased.contains spec.proof
  let specs := candidates.insertionSort fun s₁ s₂ => s₁.priority > s₂.priority
  return specs[0]?

meta def SpecializedWPApplyApp.rewriteWPApply (app : SpecializedWPApplyApp) (e : Expr) : SymM Expr := do
  let post (e : Expr) : SymM TransformStep := do
    e.withApp fun f args => do
    unless f.isConstOf ``PredTrans.apply do return .done e
    if args.size < 3 then return .done e
    let wp := args[2]!
    unless wp.isAppOfArity ``WP.wp 5 do return .done e
    let #[m, _ps, _instWP, α, prog] := wp.getAppArgs | return .done e
    unless ← isDefEqS m app.m do return .done e
    let res := mkAppN (mkConst app.name) (#[α, prog] ++ args[3...*])
    check res
    trace[Elab.Tactic.Do.vcgen] "checked result: {res}"
    return .done res
  Meta.transform e (post := post) (skipConstInApp := true)

meta def SpecTheorem.mkBackwardRuleFromSpec (specThm : SpecTheorem) (σs : Expr) (app : SpecializedWPApplyApp) : SymM BackwardRule := do
  let preprocessExpr : Expr → SymM Expr := shareCommon <=< liftMetaM ∘ unfoldReducible
  -- Create a backward rule for the spec we look up in the database.
  -- In order for the backward rule to apply, we need to instantiate both `m` and `ps` with the ones
  -- given by the use site.
  let (xs, _bs, spec, specTy) ← specThm.proof.instantiate
  let_expr f@Triple m' ps' instWP' α prog P Q := specTy
    | liftMetaM <| throwError "target not a Triple application {specTy}"
  unless ← isDefEqGuarded app.m m' do -- TODO: Try isDefEqS?
    Term.throwTypeMismatchError none app.m m' spec
  unless ← isDefEqGuarded app.ps ps' do
    Term.throwTypeMismatchError none app.ps ps' spec
  unless ← isDefEqGuarded app.instWP instWP' do
    Term.throwTypeMismatchError none app.instWP instWP' spec

  -- We must ensure that P and Q are pattern variables so that the spec matches for every potential
  -- P and Q. We do so by introducing VCs accordingly.
  -- The following code could potentially be extracted into a definition at @[spec] attribute
  -- annotation time. That might help a bit with kernel checking time.
  let excessArgNamesTypes ← app.excessArgs.mapM fun arg =>
    return (← mkFreshUserName `s, ← Sym.inferType arg)
  let spec ← withLocalDeclsDND excessArgNamesTypes fun ss => do
    let needPreVC := !xs.contains P
    let needPostVC := !xs.contains Q
    let us := f.constLevels!
    let u := us[0]!
    let wpApplyQ := mkApp3 (mkConst app.name) α prog Q  -- wp⟦prog⟧ Q
    let Pss := mkAppN P ss  -- P s₁ ... sₙ
    let typeP ← preprocessExpr (mkApp (mkConst ``SPred [u]) σs)
      -- Note that this is the type of `P s₁ ... sₙ`,
      -- which is `Assertion ps'`, but we don't know `ps'`
    let typeQ ← preprocessExpr (mkApp2 (mkConst ``PostCond [u]) α app.ps)
    let mut declInfos := #[]
    if needPreVC then
      let nmP' ← mkFreshUserName `P
      let nmHPre ← mkFreshUserName `hpre
      let entailment P' := preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs P' Pss
      declInfos := #[(nmP', .default, fun _ => pure typeP),
                     (nmHPre, .default, fun xs => entailment xs[0]!)]
    if needPostVC then
      let nmQ' ← mkFreshUserName `Q
      let nmHPost ← mkFreshUserName `hpost
      let entailment Q' := pure <| mkApp3 (mkConst ``PostCond.entails [u]) app.ps Q Q'
      declInfos := declInfos ++
                   #[(nmQ', .default, fun _ => pure typeQ),
                     (nmHPost, .default, fun xs => entailment xs[0]!)]
    withLocalDecls declInfos fun ys => liftMetaM ∘ mkLambdaFVars (ss ++ ys) =<< do
      if !needPreVC && !needPostVC && app.excessArgs.isEmpty then
        -- Still need to unfold the triple in the spec type
        let entailment ← preprocessExpr <| mkApp3 (mkConst ``SPred.entails [u]) σs P wpApplyQ
        let prf ← mkExpectedTypeHint spec entailment
        -- check prf
        return prf
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
        let wp := mkApp5 (mkConst ``WP.wp f.constLevels!) app.m app.ps app.instWP α prog
        let Q' := ys[ys.size-2]!
        let hpost := ys[ys.size-1]!
        let wpApplyQ' := mkApp3 (mkConst app.name) α prog Q' -- wp⟦prog⟧ Q'
        let wpApplyQ' := mkAppN wpApplyQ' ss -- wp⟦prog⟧ Q' s₁ ... sₙ
        let hmono := mkApp6 (mkConst ``PredTrans.mono [u]) app.ps α wp Q Q' hpost
        let hmono := mkAppN hmono ss
        prf := mkApp6 (mkConst ``SPred.entails.trans [u]) σs newP wpApplyQ wpApplyQ' prf hmono
        newQ := Q'
        -- check prf
      return prf
  let res ← abstractMVars spec
  let type ← preprocessExpr (← Sym.inferType res.expr)
  let type ← app.rewriteWPApply type
  let type ← unfoldSPredEntails type
  trace[Elab.Tactic.Do.vcgen] "Type of new auxiliary spec apply theorem: {type}"
  let spec ← Meta.mkAuxLemma res.paramNames.toList type res.expr
  mkBackwardRuleFromDecl spec

end Lean.Elab.Tactic.Do.SpecAttr

/-!
VC generation
-/

public structure VCGen.Context where
  specThms : SpecTheorems

public structure VCGen.State where
  /--
  Cached definitions wrapping `fun α x Q => @PredTrans.apply ps α (@wp m ps instWP α x) Q` with
  all reducible types reduced. Maps `m` (which uniquely identifies `ps` and `instWP`) to definition name.
  -/
  wpApplyCache : Std.HashMap Expr Name := {}
  /--
  Cached `(wp _).apply` functions in `applyCache`, indexed by `Name` and mapping to `(m, ps, instWP)`.
  -/
  wpApplyByName : Std.HashMap Name (Expr × Expr × Expr) := {}
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

@[inline]
meta def _root_.Std.HashMap.getDM [Monad m] [BEq α] [Hashable α]
    (cache : Std.HashMap α β) (key : α) (fallback : m β) : m (β × Std.HashMap α β) := do
  if let some b := cache.get? key then
    return (b, cache)
  let b ← fallback
  return (b, cache.insert key b)

meta def mkSpecializedWPApplyCached (wp : Expr) (wpRevArgs : Array Expr) : VCGenM Name := do
  let s ← get
  -- WP.wp : {m : Type u → Type v} → {ps : outParam PostShape} → [self : WP m ps] → {α : Type u} → m α → PredTrans ps α
  let m := wpRevArgs[wpRevArgs.size-1]!
  let ps := wpRevArgs[wpRevArgs.size-2]!
  let instWP := wpRevArgs[wpRevArgs.size-3]!
  let (name, wpApplyCache) ← s.wpApplyCache.getDM m (mkSpecializedWPApply wp wpRevArgs)
  let (_, wpApplyByName) ← s.wpApplyByName.getDM name (pure (m, ps, instWP))
  set { s with wpApplyCache, wpApplyByName }
  return name

meta def isSpecializedWPApplyApp (T : Expr) : VCGenM (Option SpecializedWPApplyApp) := do
  T.withAppRev fun f revArgs => do
  unless f.isConst do return none
  let name := f.constName!
  let some (m, ps, instWP) := (← get).wpApplyByName.get? name | return none
  let α := revArgs.back!; let revArgs := revArgs.pop;
  let e := revArgs.back!; let revArgs := revArgs.pop;
  let Q := revArgs.back!; let revArgs := revArgs.pop;
  let excessArgs := revArgs.reverse
  return some { name, m, ps, instWP, α, e, Q, excessArgs }

meta def mkBackwardRuleFromSpecCached (specThm : SpecTheorem) (σs : Expr) (app : SpecializedWPApplyApp) : VCGenM BackwardRule := do
  let mkRuleSlow := specThm.mkBackwardRuleFromSpec σs app
  let s ← get
  let .global decl := specThm.proof | mkRuleSlow
  let (rule, specBackwardRuleCache) ← s.specBackwardRuleCache.getDM (decl, app.m, app.excessArgs.size) mkRuleSlow
  set { s with specBackwardRuleCache }
  return rule

meta def unfoldTriple (goal : MVarId) : SymM MVarId := goal.withContext do
  let type ← goal.getType
  unless type.isAppOf ``Triple do return goal
  let type ← unfoldDefinition type
  let goal ← goal.replaceTargetDefEq type
  preprocessMVar goal  -- need to reinstate subterm sharing. TODO: replace `unfoldDefinition`?

structure SPredEntailsApp where
  /-- The level of the `SPred`. -/
  u : Level
  /-- `some σs` => `SPred.entails σs`. `none` => `nilEntails`. -/
  σs? : Option Expr
  /-- The left-hand side of the entailment. -/
  H : Expr
  /-- The right-hand side of the entailment. -/
  T : Expr

meta def SPredEntailsApp.mkApp (app : SPredEntailsApp) : Expr :=
  match app.σs? with
  | some σs => mkApp3 (mkConst ``SPred.entails [app.u]) σs app.H app.T
  | none => mkApp2 (mkConst ``nilEntails [app.u]) app.H app.T

meta def SPredEntailsApp.σs (app : SPredEntailsApp) : Expr :=
  match app.σs? with
  | some σs => σs
  | none => Do.ProofMode.TypeList.mkNil app.u

meta def SPredEntailsApp.unfold? (app : SPredEntailsApp) : Option Expr :=
  match app.σs? with
  | none => { app with σs? := some (Do.ProofMode.TypeList.mkNil app.u) }.mkApp
  | _ => none

meta def isSPredEntailsApp? (target : Expr) : Option SPredEntailsApp :=
  if target.isAppOfArity ``SPred.entails 3 then
    let u := target.getAppFn.constLevels![0]!
    let args := target.getAppArgs
    some { u, σs? := some args[0]!, H := args[1]!, T := args[2]! }
  else if target.isAppOfArity ``nilEntails 2 then
    let u := target.getAppFn.constLevels![0]!
    let args := target.getAppArgs
    some { u, σs? := none, H := args[0]!, T := args[1]! }
  else
    none

open Lean.Elab.Tactic.Do in
meta def simplifyTarget (goal : MVarId) : _root_.VCGenM MVarId := goal.withContext do
  let target ← goal.getType
  let some app := isSPredEntailsApp? target | return goal
  let some T ← reduceProjBeta? app.T | return goal -- very slight simplification
  goal.replaceTargetDefEq { app with T }.mkApp

meta def specializeWPApply (goal : MVarId) : VCGenM MVarId := goal.withContext do
  let target ← goal.getType
  let some app := isSPredEntailsApp? target | return goal
  app.T.withAppRev fun apply applyRevArgs => do
  unless apply.isConstOf ``PredTrans.apply do return goal
  applyRevArgs[applyRevArgs.size-3]!.withAppRev fun wp wpRevArgs => do
  unless wp.isConstOf ``WP.wp do return goal
  let name ← mkSpecializedWPApplyCached wp wpRevArgs
  -- The args to the specialized `wpApply` def are `[α, e, Q, s₁, ..., sₙ]`.
  -- We take `[α, e]` from `wpRevArgs[0...2].reverse`
  -- and `[Q, s₁, ..., sₙ]` from `applyRevArgs[*...applyRevArgs.size-3].reverse`.
  let T := mkAppRev (mkConst name) (applyRevArgs[*...applyRevArgs.size-3] ++ wpRevArgs[0...2])
  goal.replaceTargetDefEq { app with T }.mkApp

meta def specializeSPredEntails (goal : MVarId) : VCGenM MVarId := goal.withContext do
  let target ← goal.getType
  unless target.isAppOfArity ``SPred.entails 3 do return goal
  let target ← unfoldSPredEntails target
  goal.replaceTargetDefEq target

meta def introStates (goal : MVarId) : VCGenM MVarId := goal.withContext do
  let mut target ← goal.getType
  unless target.isForall do return goal
--  trace[Elab.Tactic.Do.vcgen] "goal is a forall: {goal}"
--  let mut forallDepth := 0
--  repeat do
--    let .forallE _ _dom rng _ := target | unreachable!
--    if !rng.isForall || rng.isAppOf ``ULift.down then break
--    forallDepth := forallDepth + 1
--    target := rng
  let IntrosResult.goal _ goal' ← Sym.intros goal | return goal
  return goal'

meta def preprocessGoal (goal : MVarId) : VCGenM (Option MVarId) := do
  let mut goal := goal
  goal ← unfoldTriple goal
  goal ← simplifyTarget goal
  goal ← specializeWPApply goal
  goal ← specializeSPredEntails goal
  goal ← introStates goal
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
  let some entailsApp := isSPredEntailsApp? target | return .noEntailment target
  -- The goal is of the form `H ⊢ₛ T`. Look for program syntax in `T`.

  if entailsApp.T.isLambda then
    -- This happens after applying the `get` spec. We have `T = fun s => wp⟦.. s⟧ Q s`.
    -- Do what `mIntroForall` does, that is, eta-expand. Note that this introduces an
    -- excess state arg `s`.
    let .goal _ goal ← Sym.introN goal 1 | return .noEntailment target
    return .goals [goal]

  let res? ← isSpecializedWPApplyApp entailsApp.T
  trace[Elab.Tactic.Do.vcgen] "Monad of specialized wp apply app: {SpecializedWPApplyApp.m <$> res?}"
  let some wpApp@{ name, m, ps, instWP, α, e, Q, excessArgs : SpecializedWPApplyApp } := res?
        | return .noProgramFoundInTarget entailsApp.T
  -- `T` is defeq to the form `wp⟦e⟧ Q s₁ ... sₙ`, where `e` is the program.
  -- We call `s₁ ... sₙ` the excess state args; the backward rules need to account for these.
  -- Excess state args are introduced by the spec of `get` (see lambda case above).
  let f := e.getAppFn
  withTraceNode `Elab.Tactic.Do.vcgen (msg := fun _ => return m!"Program: {e}") do

  -- Apply registered specifications.
  if f.isConst || f.isFVar then
    trace[Elab.Tactic.Do.vcgen] "Applying a spec for {e}. Excess args: {excessArgs}"
    let some thm ← (← read).specThms.findSpec e
      | return .noSpecFoundForProgram e
    let rule ← mkBackwardRuleFromSpecCached thm entailsApp.σs wpApp
    let ApplyResult.goals goals ← rule.apply goal
      | throwError "Failed to apply rule {thm.proof} for {e}"
    return .goals goals

  return .noStrategyForProgram e

meta def unfoldSpecializedDefs (goal : MVarId) : VCGenM MVarId := goal.withContext do
  let post (e : Expr) : VCGenM TransformStep := do
    if let some e := isSPredEntailsApp? e >>= SPredEntailsApp.unfold? then
      return .done e
    else if let some app ← isSpecializedWPApplyApp e then
      return .done (← app.unfold)
    else
      return .done e
  goal.replaceTargetDefEq (← transform (← goal.getType) (post := post) (skipConstInApp := true))

meta def emitVC (goal : MVarId) : VCGenM Unit := do
  let goal ← unfoldSpecializedDefs goal
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
    trace[Elab.Tactic.Do.vcgen] "preprocessed goal: {goal}"
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
  return { specThms }

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

-- set_option trace.Elab.Tactic.Do.vcgen true in
set_option diagnostics true in
example : ∀ post, ⦃post⦄ loop 500 ⦃⇓_ => post⦄ := by
  intro post
  simp only [loop, step]
  mvcgen'
  grind
