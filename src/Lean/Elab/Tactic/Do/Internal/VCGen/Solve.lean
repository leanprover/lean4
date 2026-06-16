/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf, Vladimir Gladshtein
-/
module

prelude
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.RuleCache
public import Lean.Elab.Tactic.Do.Internal.VCGen.Entails
public import Lean.Meta.Sym.InstantiateS
import Lean.Meta.Sym.InferType

open Lean Meta Elab Tactic Sym Sym.Internal
open Lean.Elab.Tactic.Do.Internal.SpecAttr
open Lean.Elab.Tactic.Do.Internal
open Std.Internal.Do Lean.Order

namespace Lean.Elab.Tactic.Do.Internal

/-!
The main `solve` step. Runs once per worklist iteration and either fully
decomposes the current goal into subgoals, or reports why no further
progress is possible (`SolveResult`).
-/

namespace VCGen

/-- The reason why no further VC generation progress is possible on the current goal. -/
public inductive SolveResult.StopReason where
  /-- Out of fuel. -/
  | outOfFuel
  /-- `until <pat>` matched. -/
  | untilPatternMatched (m : Expr)
  /-- The target was not of the form `pre ⊑ rhs`. -/
  | noEntailment (target : Expr)
  /-- The target was of the form `pre ⊑ rhs`, but we couldn't make further progress. -/
  | noProgress (pre rhs : Expr)

/-- The result of one `solve` step of VC generation. -/
public inductive SolveResult where
  /-- Successfully decomposed the goal. These are the subgoals, sharing `scope`. -/
  | goals (scope : VCGen.Scope) (subgoals : List MVarId)
  /--
  Did not find a spec for the `e` in `pre ⊑ wp e post epost s₁ ... sₙ`.
  Candidates were `thms`, but none of them matched the monad.
  -/
  | noSpecFoundForProgram (e : Expr) (monad : Expr) (thms : Array SpecTheorem)
  /-- No further progress possible on the current goal for the given reason. Emit goal as VC. -/
  | stop (reason : SolveResult.StopReason)

private def isDuplicable (e : Expr) : Bool := match e with
  | .bvar .. | .mvar .. | .fvar .. | .const .. | .lit .. | .sort .. => true
  | .mdata _ e | .proj _ _ e => isDuplicable e
  | .lam .. | .forallE .. | .letE .. => false
  | .app .. => e.isAppOf ``OfNat.ofNat

/-- Strategy 1: simp the target, then introduce binders if the target is a `∀`. -/
private def forallIntro? (goal : MVarId) (target : Expr) : VCGenM (Option (List MVarId)) := do
  unless target.isForall do return none
  let (goal, simped) ← match ← simpGoalTelescope goal with
    | .closed => return some []
    | .goal goal' => pure (goal', true)
    | .noProgress => pure (goal, false)
  let goal' ← introsHygienic goal
  if !simped && goal' == goal then
    throwError "Failed to intro forall target {goal}"
  return some [goal']

private def throwIfUnsupportedJP (name : Name) (val : Expr) : VCGenM Unit := do
  if (← read).useJP && Lean.Elab.Tactic.Do.isJP name && val.isLambda then
    throwError "mvcgen': shared-continuation handling for `__do_jp` is not yet \
      implemented. Detection point reached at {name}; the upstream \
      `Lean.Elab.Tactic.Do.onJoinPoint` (`src/Lean/Elab/Tactic/Do/VCGen.lean:215`) \
      needs to be ported to the worklist style. Drop `(jp := true)` to fall back \
      to the default zeta-unfold behaviour."

/-- Strategy 2: zeta-substitute a duplicable top-level `let` in the target, otherwise
introduce it into the local context. -/
private def targetLetIntro? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let .letE name _ val body _ := target | return none
  throwIfUnsupportedJP name val
  if isDuplicable val then
    trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {name}"
    return some (← goal.replaceTargetDefEq (← Sym.instantiateRevBetaS body #[val]))
  else
    trace[Elab.Tactic.Do.vcgen] "let-intro: {name}"
    return some (← introsHygienic goal)

/-- Strategy 3: unfold a `Triple` target into the underlying lattice entailment. -/
private def tripleUnfold? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  unless target.isAppOf ``Triple do return none
  return some (← unfoldTriple goal)

/-- Extract the weakest-precondition metadata from the RHS of a lattice entailment. -/
private def getWPInfo? (rhs : Expr) : Option WPInfo :=
  rhs.withApp fun head args =>
    if head.isConstOf ``Std.Internal.Do.wp && args.size ≥ 11 then
      some { head, args := args.take 11, excessArgs := args.drop 11 }
    else
      none

/-- Strategy 3b: turn a bare `wp` application target (a `Prop`) into `⊤ ⊑ wp …`. Entry-point
goals produced by the `of_wp_run_eq` lemmas have this shape. -/
private def bareWPToLe? (goal : MVarId) (target : Expr) : VCGenM (Option MVarId) := do
  let some _ := getWPInfo? target | return none
  let newTarget ← mkAppM ``PartialOrder.rel #[← mkAppOptM ``Lean.Order.top #[mkSort 0, none], target]
  let newTarget ← shareCommon newTarget
  let g ← liftMetaM <| mkFreshExprSyntheticOpaqueMVar newTarget
  goal.assign (mkApp2 (mkConst ``Lean.Order.of_top_le_prop) target g)
  return some g.mvarId!

/-- Strategy 4: close a reflexive entailment `pre ⊑ pre` by applying `PartialOrder.rel_refl`.
Runs before the precondition lift so a spec handoff `pre ⊑ specPre` closes by unification rather
than an assumption search. The pattern matcher keeps synthetic-opaque invariant holes rigid, so
`⊤ ⊑ ?inv args` is left untouched. -/
private def rfl? (goal : MVarId) : VCGenM (Option (List MVarId)) := do
  let .goals gs ← (← read).reflRule.apply goal | return none
  trace[Elab.Tactic.Do.vcgen] "Solved by rfl {goal}"
  return some gs

/-- Strategy 10: close `pre ⊑ φ` on the `Prop` lattice against the most recently lifted pure
precondition, cached in `Scope.lastLiftedPre?`. Runs after lattice decomposition, so `φ` is an
opaque proposition rather than a lattice connective. This is one defeq check against one
hypothesis, not an assumption search.

Goals whose RHS contains metavariables are skipped: the defeq check could otherwise assign
a post abstraction from an unrelated hypothesis. -/
private def liftedHyp? (scope : VCGen.Scope) (goal : MVarId) (α pre rhs : Expr) :
    VCGenM (Option (List MVarId)) :=
  goal.withContext do
    unless α.isProp do return none
    if rhs.hasExprMVar then return none
    let some fvarId := scope.lastLiftedPre? | return none
    let some hyp := (← getLCtx).find? fvarId | return none
    unless ← isDefEqS rhs hyp.type do return none -- TODO: Replace with isSameExpr test?
    trace[Elab.Tactic.Do.vcgen] "Solved by lifted hypothesis {hyp.userName}"
    goal.assign (← mkAppM ``Lean.Order.le_of_right #[pre, rhs, hyp.toExpr])
    return some []

/-- Close a bare `Prop` residual, such as the subgoal of the `⌜φ⌝` lattice rule, against the
most recently lifted pure precondition. Runs when the target is not a lattice entailment,
just before it would be classified as a VC. -/
private def liftedHypBare? (scope : VCGen.Scope) (goal : MVarId) (target : Expr) :
    VCGenM (Option (List MVarId)) :=
  goal.withContext do
    if target.hasExprMVar then return none
    let some fvarId := scope.lastLiftedPre? | return none
    let some hyp := (← getLCtx).find? fvarId | return none
    unless ← isDefEqS target hyp.type do return none -- TODO: Replace with isSameExpr test?
    trace[Elab.Tactic.Do.vcgen] "Solved by lifted hypothesis {hyp.userName}"
    goal.assign hyp.toExpr
    return some []

/-- Strategy 5: cancel a redundant `P ⊓ ⊤` precondition via `meet_top_le_of_le`, leaving `P ⊑ rhs`.
Such a precondition arises when `himp_complete` splits `⊤ ⊑ a ⇨ b` into `a ⊓ ⊤ ⊑ b`. -/
private def stripMeetTopPre? (goal : MVarId) (pre : Expr) : VCGenM (Option MVarId) := do
  let_expr Lean.Order.meet _l _inst _P top := pre | return none
  unless top.isAppOf ``Lean.Order.top do return none
  let .goals [g] ← (← read).meetTopRule.applyChecked goal
    | throwError "Failed to cancel the `⊓ ⊤` precondition of {goal}"
  return some g

/-- Strategy 5: lift an embedded pure precondition `⌜φ⌝` into the local context, leaving `⊤`
as the residual precondition. Runs before state-argument introduction, which would otherwise
leave `⌜φ⌝` applied to the introduced arguments. Returns the new goal and the hypothesis. -/
private def ofPropPreIntro? (goal : MVarId) (pre : Expr) : VCGenM (Option (MVarId × FVarId)) := do
  let_expr CompleteLattice.ofProp _l _inst φ := pre | return none
  if φ.isTrue then return none
  return some (← introPre (← read).introRules.ofPropPreIntro goal)

/-- Strategy 7: move a bare `Prop` precondition `φ ⊑ rhs` into the local context via
`le_of_imp_top_le`, leaving `⊤ ⊑ rhs`. Runs after `True` and `⊤` preconditions are handled, so
`φ` carries information worth keeping. Returns the new goal and the introduced hypothesis. -/
private def barePreIntro? (goal : MVarId) (α pre : Expr) : VCGenM (Option (MVarId × FVarId)) := do
  unless α.isProp do return none
  if pre.isAppOf ``Lean.Order.top then return none
  return some (← introPre (← read).introRules.propPreIntro goal)

/-- Strategy 7: replace a `True` precondition by `⊤` via `true_le_of_top_le`, so the goal
follows the `⊤` path instead of lifting `True` into the local context. -/
private def truePre? (goal : MVarId) (pre target : Expr) : VCGenM (Option (List MVarId)) := do
  unless pre.isTrue do return none
  let .goals [g] ← (← read).introRules.truePreIntro.applyChecked goal
    | throwError "Failed to apply {.ofConstName ``Lean.Order.true_le_of_top_le} to{indentExpr target}"
  return some [g]

/-- Phase 2: drive the precondition of `pre ⊑ rhs` toward `⊤`, lifting any pure content into the
local context so a later spec application sees a `⊤` precondition. In order: cancel a redundant
`⊓ ⊤`; lift an embedded `⌜φ⌝` (before state-argument introduction, which would otherwise leave
`⌜φ⌝` applied to the introduced state); introduce excess state arguments; drop a `True`
precondition; lift a bare `Prop` precondition. Returns the updated scope, recording any lifted
hypothesis. -/
private def normalizePre? (scope : VCGen.Scope) (goal : MVarId) (α pre target : Expr) :
    VCGenM (Option (VCGen.Scope × List MVarId)) := do
  if let some g ← stripMeetTopPre? goal pre then
    return some (scope, [g])
  if let some (g, h) ← ofPropPreIntro? goal pre then
    return some ({ scope with lastLiftedPre? := some h }, [g])
  if α.isForall then
    return some (scope, [← introsExcessArgs goal])
  if let some gs ← truePre? goal pre target then
    return some (scope, gs)
  if let some (g, h) ← barePreIntro? goal α pre then
    return some ({ scope with lastLiftedPre? := some h }, [g])
  return none

/-- Replace the program in `goal`'s target with `prog` (which must be definitionally equal). -/
private def replaceProgDefEq (goal : MVarId) (target : Expr) (info : WPInfo) (prog : Expr) :
    VCGenM MVarId := do
  let wp ← mkAppNS info.head <| info.args.set! 8 prog
  let rhs ← mkAppNS wp info.excessArgs
  let relArgs := target.getAppArgs
  let newTarget ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) rhs)
  goal.replaceTargetDefEq newTarget

/-- Strategy 11a: hoist or zeta-substitute a `let` from the program head. -/
private def wpLet? (goal : MVarId) (target : Expr) (info : WPInfo) : VCGenM (Option MVarId) := do
  let .letE name type val body nondep := info.prog.getAppFn | return none
  let appArgs := info.prog.getAppRevArgs
  throwIfUnsupportedJP name val
  if isDuplicable val then
    trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {name}"
    let body' ← Sym.instantiateRevBetaS body #[val]
    let prog ← mkAppRevS body' appArgs
    return some (← replaceProgDefEq goal target info prog)
  else
    trace[Elab.Tactic.Do.vcgen] "let-hoist: {name}"
    let prog ← mkAppRevS body appArgs
    let wp ← mkAppNS info.head <| info.args.set! 8 prog
    let rhs ← mkAppNS wp info.excessArgs
    let relArgs := target.getAppArgs
    let target ← mkAppNS target.getAppFn (relArgs.set! (relArgs.size - 1) rhs)
    let target := Expr.letE name type val target nondep
    let goal ← goal.replaceTargetDefEq target
    let .goal _ goal ← Sym.intros goal
      | throwError "Failed to intro hoisted let"
    return some goal

/-- Strategy 11b: split an `ite`/`dite`/match program, or iota-reduce a matcher with a concrete
discriminant. -/
private def wpMatch? (goal : MVarId) (target : Expr) (info : WPInfo) :
    VCGenM (Option (List MVarId)) := do
  let some splitInfo ← liftMetaM <| Lean.Elab.Tactic.Do.getSplitInfo? info.prog | return none
  if splitInfo matches .matcher .. then
    if let some prog ← liftMetaM <| withReducible <| reduceRecMatcher? info.prog then
      return some [← replaceProgDefEq goal target info (← shareCommonInc prog)]
  let rule ← mkBackwardRuleForSplitCached splitInfo info
  let .goals goals ← rule.applyChecked goal m!"split rule for{indentExpr info.prog}"
    | throwError "Failed to apply split rule for {indentExpr info.prog}"
  let mut simpGoals := #[]
  for g in goals do
    match ← simpGoalTelescope g with
    | .goal g' => simpGoals := simpGoals.push g'
    | .noProgress => simpGoals := simpGoals.push g
    | .closed => continue
  return some simpGoals.toList

/-- Strategy 11c: zeta-unfold a local let-bound fvar used as the program head. -/
private def wpFVarZeta? (goal : MVarId) (target : Expr) (info : WPInfo) :
    VCGenM (Option MVarId) := do
  let f := info.prog.getAppFn
  let some fvarId := f.fvarId? | return none
  let some val ← fvarId.getValue? | return none
  trace[Elab.Tactic.Do.vcgen] "fvar-zeta: {(← fvarId.getUserName)}"
  let prog ← shareCommonInc (val.betaRev info.prog.getAppRevArgs)
  return some (← replaceProgDefEq goal target info prog)

/-- Strategy 11d: reduce a projection head in the program. -/
private def wpHeadReduce? (goal : MVarId) (target : Expr) (info : WPInfo) :
    VCGenM (Option MVarId) := do
  let f := info.prog.getAppFn
  unless f matches .proj .. do return none
  let some f' ← withReducibleAndInstances (reduceProj? f) | return none
  let f' ← shareCommon (← liftMetaM <| unfoldReducible f')
  let prog ← betaRevS f' info.prog.getAppRevArgs
  return some (← replaceProgDefEq goal target info prog)

/-- Strategy 11e: look up a registered `@[spec]` theorem (triple or simp) for the program head
and apply its cached backward rule. -/
private def applySpec (scope : VCGen.Scope) (goal : MVarId) (target : Expr) (info : WPInfo) :
    VCGenM SolveResult := do
  trace[Elab.Tactic.Do.vcgen] "Applying a spec for {info.prog}. Excess args: {info.excessArgs}"
  match ← SpecTheorems.findSpecs scope.specs info.prog with
  | .error thms => return .noSpecFoundForProgram info.prog info.m thms
  | .ok thm =>
  trace[Elab.Tactic.Do.vcgen] "Spec for {info.prog}: {thm.proof}"
  let some rule ←
    try
      mkBackwardRuleFromSpecCached thm info |>.run
    catch ex =>
      throwError "Failed to construct rule {thm.proof} for {indentExpr info.prog}\n\
        error: {ex.toMessageData}\n\
        target:{indentExpr target}\n\
        Pred:{indentExpr info.Pred}\n\
        excessArgs: {info.excessArgs}"
    | return .noSpecFoundForProgram info.prog info.m #[thm]
  let .goals goals ← rule.applyChecked goal m!"spec rule for{indentExpr info.prog}"
    | do
      let ruleType ← Meta.inferType rule.expr
      throwError "Failed to apply rule {thm.proof} for {indentExpr info.prog}\n\
        target:{indentExpr target}\n\
        Pred:{indentExpr info.Pred}\n\
        excessArgs: {info.excessArgs}\n\
        rule type:{indentExpr ruleType}"
  return .goals scope goals

/-- True iff the program matches the `until` pattern (elaborated lazily against the program
monad), in which case VC generation stops at this goal. -/
private def matchesUntilPattern (m prog : Expr) : VCGenM Bool := do
  let some ref := (← read).untilPat? | return false
  let pat ← UntilPatternThunk.force ref m
  if (← pat.match? prog).isSome then
    trace[Elab.Tactic.Do.vcgen] "`until` pattern matched program {prog}; stopping"
    return true
  return false

/--
The main VC generation step. Operates on a plain `MVarId` with no knowledge of grind.
Returns `.goals subgoals` when the goal was decomposed, or a classification result
(`.noEntailment`, `.noProgramOrLatticeFoundInTarget`, etc.) when no further decomposition is
possible.

The function performs the following steps in order:

1. **Forall introduction**: If the target is a `∀`, simp it and introduce binders.
2. **Target-let handling**: zeta-substitute duplicable top-level lets, otherwise introduce them.
3. **Triple unfolding**: If the target is `⦃P⦄ x ⦃Q; E⦄`, unfold into `P ⊑ wp x Q E`.
4. **Syntactic rfl**: close `pre ⊑ rhs` by `PartialOrder.rel_refl` when both sides unify.
5. **Embedded pure precondition introduction**: lift a `⌜φ⌝` precondition into the local
   context, before state-argument introduction would apply it to the introduced arguments.
6. **State-argument introduction**: If the lattice carrier is a function type
   `σ₁ → ... → σₙ → Base`, introduce all excess state arguments.
7. **Bare pure precondition introduction**: on the `Prop` lattice, replace a `True`
   precondition by `⊤` and lift any other precondition into the local context.
8. **EPost projection reduction**: reduce an `EPost.Cons.head` RHS to the projected component.
9. **Lattice decomposition**: decompose `⊓`, `⇨`, `⌜p⌝` and `⊤` RHS connectives.
10. **Lifted-hypothesis discharge**: close a residual `pre ⊑ ⌜φ⌝` entailment against the most
    recently lifted precondition `h : φ` in the local context, cached in `Scope.lastLiftedPre?`.
11. **WP decomposition**: when the RHS is `wp e post epost s₁ ... sₙ`, in order:
    hoist/zeta program-head lets, split `ite`/`dite`/match, zeta-unfold fvar program heads,
    reduce projection heads, and finally apply a registered `@[spec]` theorem.
-/
public def solve (scope : VCGen.Scope) (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  if ← outOfFuel then return .stop .outOfFuel
  let mut goal := goal
  let mut target ← goal.getType
  trace[Elab.Tactic.Do.vcgen] "🎯 Target: {target}"

  if target.hasExprMVar then
    -- Rule application may have assigned metavariables in the target; re-normalise so the
    -- syntactic shape tests below see the assigned form.
    target ← instantiateMVars target
    goal ← goal.replaceTargetDefEq target

  -- Phase 1: simplify `target` until it is of the form `pre ⊑ rhs`.
  if let some gs ← forallIntro? goal target then return .goals scope gs
  if let some g ← targetLetIntro? goal target then return .goals scope [g]
  if let some g ← tripleUnfold? goal target then return .goals scope [g]
  if let some g ← bareWPToLe? goal target then return .goals scope [g]

  let_expr PartialOrder.rel α inst pre rhs := target
    | if let some gs ← liftedHypBare? scope goal target then return .goals scope gs
      else return .stop (.noEntailment target)

  -- Phase 2: close reflexive goals, then drive `pre` toward `⊤`, lifting any pure content so a
  -- later spec application sees a `⊤` precondition.
  if let some gs ← rfl? goal then return .goals scope gs
  if let some (scope, gs) ← normalizePre? scope goal α pre target then return .goals scope gs

  -- Collect new local specs before any strategy that may emit multiple subgoals
  -- (`wpMatch?`, `splitLatticeOp?`) or apply a registered spec (`applySpec`).
  let scope ← scope.collectLocalSpecs goal

  -- Phase 3: shape the `rhs` (reduce an EPost projection, decompose a lattice connective), then
  -- discharge a residual entailment against the lifted hypothesis.
  if let some g ← reduceEPostHead? goal target α inst pre rhs then return .goals scope [g]
  if let some gs ← splitLatticeOp? goal rhs then return .goals scope gs
  if let some gs ← liftedHyp? scope goal α pre rhs then return .goals scope gs

  -- Phase 4: wp decomposition. The program-shape steps below all consume one unit of fuel
  -- (the `stepLimit` config option) when they make progress.
  if let some info := getWPInfo? rhs then
    trace[Elab.Tactic.Do.vcgen] "📜 Program: {info.prog}"
    -- Stop if the program matches the `until` pattern.
    if ← matchesUntilPattern info.m info.prog then
      return .stop (.untilPatternMatched info.m)
    if let some g ← wpLet? goal target info then
      VCGen.burnOne
      return .goals scope [g]
    if let some gs ← wpMatch? goal target info then
      VCGen.burnOne
      return .goals scope gs
    if let some g ← wpFVarZeta? goal target info then
      VCGen.burnOne
      return .goals scope [g]
    if let some g ← wpHeadReduce? goal target info then
      VCGen.burnOne
      return .goals scope [g]
    let f := info.prog.getAppFn
    if f.isConst || f.isFVar then
      VCGen.burnOne
      return ← applySpec scope goal target info
    throwError "Failed to decompose weakest precondition for {info.prog}. This should not happen."

  return .stop (.noProgress pre rhs)

end VCGen

end Lean.Elab.Tactic.Do.Internal
