/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Elab
public import Lean.Meta
public meta import Lean.Elab
public meta import Lean.Meta
public meta import Lean.Meta.Match.Rewrite
public meta import Lean.Elab.Tactic.Do.VCGen.Split
public meta import VCGen.Context
public meta import VCGen.Reduce
public meta import VCGen.Util
public meta import VCGen.RuleCache
public meta import VCGen.Entails

open Lean Meta Elab Tactic Sym Sym.Internal
open Lean.Elab.Tactic.Do.SpecAttr
open Std.Do


/-!
The main `solve` step. Runs once per worklist iteration and either fully
decomposes the current goal into subgoals, or reports why no further
progress is possible (`SolveResult`).
-/

namespace VCGen

public inductive SolveResult where
  /-- `target` was not of the form `H ⊢ₛ T`. -/
  | noEntailment (target : Expr)
  /-- The `T` in `H ⊢ₛ T` was not of the form `wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noProgramFoundInTarget (T : Expr)
  /-- Don't know how to handle `e` in `H ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ`. -/
  | noStrategyForProgram (e : Expr)
  /--
  Did not find a spec for the `e` in `H ⊢ₛ wp⟦e⟧ Q s₁ ... sₙ`.
  Candidates were `thms`, but none of them matched the monad.
  -/
  | noSpecFoundForProgram (e : Expr) (monad : Expr) (thms : Array SpecTheoremNew)
  /-- Successfully decomposed the goal. These are the subgoals. -/
  | goals (subgoals : List MVarId)

private meta def isDuplicable (e : Expr) : Bool := match e with
  | .bvar .. | .mvar .. | .fvar .. | .const .. | .lit .. | .sort .. => true
  | .mdata _ e | .proj _ _ e => isDuplicable e
  | .lam .. | .forallE .. | .letE .. => false
  | .app .. => e.isAppOf ``OfNat.ofNat

/-- Strategy 1: introduce binders if the target is a `∀`. -/
private meta def tryForallIntro (goal : MVarId) (target : Expr) :
    VCGenM (Option SolveResult) := do
  unless target.isForall do return none
  return some <| .goals [← introsSimp goal m!"foralls in `solve`"]

/-- Strategy 7a: zeta-substitute (if the bound value is duplicable) or introduce a
top-level `let` in the target.

When `Context.useJP` is set and the let binds a `__do_jp` (do-elaborator-emitted
shared continuation) whose value is a function whose body is a splitter, we are
at the point where the upstream `mvcgen.onJoinPoint` would set up shared-continuation
proof construction. That port (Phase 6 of the plan) is not yet done; we throw an
explicit error here so that enabling `jp := true` is honest about the gap rather
than silently ignored. -/
private meta def tryLetIntro (goal : MVarId) (target : Expr) :
    VCGenM (Option SolveResult) := do
  unless target.isLet do return none
  if (← read).useJP && Lean.Elab.Tactic.Do.isJP target.letName! then
    if target.letValue!.isLambda then
      throwError "mvcgen': shared-continuation handling for `__do_jp` is not yet \
        implemented. Detection point reached at {target.letName!}; the upstream \
        `Lean.Elab.Tactic.Do.onJoinPoint` (`src/Lean/Elab/Tactic/Do/VCGen.lean:215`) \
        needs to be ported to the worklist style. Drop `(jp := true)` to fall back \
        to the default zeta-unfold behaviour."
  if isDuplicable target.letValue! then
    trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {target.letName!}"
    let target' ← Sym.instantiateRevBetaS target.letBody! #[target.letValue!]
    return some <| .goals [← goal.replaceTargetDefEq target']
  else
    trace[Elab.Tactic.Do.vcgen] "let-intro: {target.letName!}"
    return some <| .goals [← introsSimp goal m!"let-intro: {target.letName!}"]

/-- Strategy 2: unfold a `Triple` target into the underlying `P ⊢ₛ wp⟦x⟧ Q`. -/
private meta def tryTripleUnfold (goal : MVarId) (target : Expr) :
    VCGenM (Option SolveResult) := do
  unless target.getAppFn.isConstOf ``Triple do return none
  let goal ← tripleOfWP goal
  return some <| .goals [goal]

/-- Strategy 4: eta-expand a lambda RHS via `entails_cons_intro`. -/
private meta def tryTargetLambdaIntro (goal : MVarId) (T : Expr) :
    VCGenM (Option SolveResult) := do
  unless T.isLambda do return none
  let .goals [goal] ← (← read).entailsConsIntroRule.apply goal
    | throwError "Applying {.ofConstName ``SPred.entails_cons_intro} to {← goal.getType} failed. It should not."
  return some <| .goals [goal]

/-- Strategy 5: head-reduce `H` and/or `T` and replace the target if either side reduced. -/
private meta def tryHeadReduceHT (goal : MVarId) (ent σs H T : Expr) :
    VCGenM (Option SolveResult) := do
  let H? ← reduceHead? H
  let T? ← reduceHead? T
  unless H?.isSome || T?.isSome do return none
  let goal ← goal.replaceTargetDefEq (← Sym.Internal.mkAppS₃ ent σs (H?.getD H) (T?.getD T))
  return some <| .goals [goal]

/-- Strategy 6: when the target's RHS isn't `wp⟦e⟧ Q s₁ ... sₙ`, attempt syntactic
reflexivity, fall back to `solveSPredEntails`, otherwise classify as
`.noProgramFoundInTarget`. -/
private meta def tryRflOrSPred (goal : MVarId) (ent σs H T : Expr) :
    VCGenM SolveResult := do
  trace[Elab.Tactic.Do.vcgen] "Trying rfl {goal}"
  if ← withAssignableSyntheticOpaque <| isDefEqS H T then
    trace[Elab.Tactic.Do.vcgen] "Solved by rfl {goal}"
    goal.assign (mkApp2 (mkConst ``SPred.entails.refl ent.constLevels!) σs H)
    return .goals []
  if let some goal ← solveSPredEntails goal then
    return .goals [goal]
  return .noProgramFoundInTarget T

/-- Replace the program in `goal`'s target with `e'` (which must be definitionally equal). -/
private meta def replaceProgDefEq (goal : MVarId) (head H σs ent : Expr) (args : Array Expr)
    (wpConst m ps instWP α e' : Expr) : VCGenM MVarId := do
  let wp ← Sym.Internal.mkAppS₅ wpConst m ps instWP α e'
  let T ← mkAppNS head (args.set! 2 wp)
  let target ← mkAppS₃ ent σs H T
  goal.replaceTargetDefEq target

/-- Hoist a `letE` from the program head to the goal target. -/
private meta def tryLetHoist (goal : MVarId) (head H σs ent : Expr) (args : Array Expr)
    (wpConst m ps instWP α e f : Expr) : VCGenM (Option SolveResult) := do
  let .letE x ty val body nonDep := f | return none
  trace[Elab.Tactic.Do.vcgen] "let-hoist: {x}"
  let e' ← mkAppRevS body e.getAppRevArgs  -- body still has #0 for the let-bound var
  let wp' ← Sym.Internal.mkAppS₅ wpConst m ps instWP α e'
  let T' ← mkAppNS head (args.set! 2 wp')
  let target' ← mkAppS₃ ent σs H T'
  let hoisted := Expr.letE x ty val target' nonDep
  return some <| .goals [← goal.replaceTargetDefEq hoisted]

/-- Split an `ite`/`dite`/match program head, or iota-reduce if the discriminant is
constructor-shaped. Returns `none` when the program isn't a split. -/
private meta def trySplit (goal : MVarId) (head H σs ent : Expr) (args : Array Expr)
    (wpConst m ps instWP α e : Expr) (excessArgs : Array Expr) : VCGenM (Option SolveResult) := do
  let some info ← liftMetaM <| Lean.Elab.Tactic.Do.getSplitInfo? e | return none
  -- Try iota reduction first (reduces matcher/recursor with concrete discriminant)
  if let some e' ← liftMetaM <| withReducible <| reduceRecMatcher? e then
    return some <| .goals [← replaceProgDefEq goal head H σs ent args wpConst m ps instWP α
                              (← shareCommonInc e')]
  let rule ← mkBackwardRuleFromSplitInfoCached info m σs ps instWP excessArgs
  let ApplyResult.goals goals ← rule.apply goal
    | throwError "Failed to apply split rule for {indentExpr e}"
  return some <| .goals goals

/-- Zeta-unfold a local `let`-bound fvar that appears as the program head. -/
private meta def tryFvarZeta (goal : MVarId) (head H σs ent : Expr) (args : Array Expr)
    (wpConst m ps instWP α e f : Expr) : VCGenM (Option SolveResult) := do
  let some fvarId := f.fvarId? | return none
  let some val ← fvarId.getValue? | return none
  trace[Elab.Tactic.Do.vcgen] "fvar-zeta: {(← fvarId.getUserName)}"
  let e' ← shareCommonInc (val.betaRev e.getAppRevArgs)
  return some <| .goals [← replaceProgDefEq goal head H σs ent args wpConst m ps instWP α e']

/-- Look up a registered `@[spec]` theorem for the program head and apply its cached
backward rule. Falls back to `.noSpecFoundForProgram` / `.noStrategyForProgram` when no
spec applies. -/
private meta def applySpec (goal : MVarId) (e : Expr) (excessArgs : Array Expr)
    (m σs ps instWP : Expr) : VCGenM SolveResult := do
  let f := e.getAppFn
  if f.isConst || f.isFVar then
    trace[Elab.Tactic.Do.vcgen] "Applying a spec for {e}. Excess args: {excessArgs}"
    match ← (← read).specThms.findSpecs e with
    | .error thms => return .noSpecFoundForProgram e m thms
    | .ok thm =>
    trace[Elab.Tactic.Do.vcgen] "Spec for {e}: {thm.proof}"
    if let some goal ← neededStateIntro thm goal excessArgs then
      trace[Elab.Tactic.Do.vcgen] "Needed state intro. Retrying."
      return .goals [goal]
    let rule ← mkBackwardRuleFromSpecCached thm m σs ps instWP excessArgs
    trace[Elab.Tactic.Do.vcgen] "Rule type: {← Meta.inferType rule.expr}"
    let ApplyResult.goals goals ← rule.apply goal
      | throwError "Failed to apply rule {rule.expr} for {indentExpr e}"
    return .goals goals
  return .noStrategyForProgram e

/--
The main VC generation step. Operates on a plain `MVarId` with no knowledge of grind.
Returns `.goals subgoals` when the goal was decomposed, or a classification result
(`.noEntailment`, `.noProgramFoundInTarget`, etc.) when no further decomposition is possible.

The function performs the following steps in order:

1. **Forall introduction**: If the target is a `∀`, introduce binders via `Sym.intros`.
2. **Triple unfolding**: If the target is `⦃P⦄ x ⦃Q⦄`, unfold into `P ⊢ₛ wp⟦x⟧ Q`.
3. **PostCond.entails decomposition**: Split `PostCond.entails` into its components.
4. **Lambda introduction**: If the RHS `T` in `H ⊢ₛ T` is a lambda, introduce an extra state
   variable via `SPred.entails_cons_intro`.
5. **Proj/beta reduction**: Reduce `Prod.fst`/`Prod.snd` projections and beta redexes in
   both `H` and `T` (e.g., `(fun _ => T, Q.snd).fst s` → `T`).
6. **Syntactic rfl**: If `T` is not a `PredTrans.apply`, try closing by `SPred.entails.refl`.
7. **Let-hoisting**: Hoist let-expressions from the program head to the goal target.
7a. **Let-zeta/intro**: If the target starts with `let`, zeta immediately if duplicable, else
    introduce into the local context via `introsSimp`.
7b. **Fvar zeta**: Unfold local let-bound fvars on demand when they appear as the program head.
8. **Iota reduction**: Reduce matchers/recursors with concrete discriminants.
9. **ite/dite/match splitting**: Apply the appropriate split backward rule.
10. **Spec application**: Look up a registered `@[spec]` theorem (triple or simp) and apply
    its cached backward rule.
-/
public meta def solve (goal : MVarId) : VCGenM SolveResult := goal.withContext do
  let target ← goal.getType
  trace[Elab.Tactic.Do.vcgen] "🎯 Target: {target}"
  -- Phase 1: simplify `target` until it is of the form `H ⊢ₛ T`.
  if let some r ← tryForallIntro goal target then return r
  if let some r ← tryLetIntro goal target then return r
  if let some r ← tryTripleUnfold goal target then return r
  if let some goals ← solvePostCondEntails goal then return .goals goals

  let_expr ent@SPred.entails σs H T := target | return .noEntailment target
  -- Phase 2: simplify `H`/`T` so that neither is a head redex and `T` is of the form
  -- `wp⟦e⟧ Q s₁ ... sₙ`.
  if let some r ← tryTargetLambdaIntro goal T then return r
  if let some r ← tryHeadReduceHT goal ent σs H T then return r

  -- Look for program syntax in `T`.
  let (head, args) := T.withApp fun head args => (head, args) -- (head, args) for nicer stack traces

  unless head.isConstOf ``PredTrans.apply do
    return ← tryRflOrSPred goal ent σs H T

  let wp := args[2]!
  let_expr wpConst@WP.wp m ps instWP α e := wp | return .noProgramFoundInTarget T
  -- `T` is of the form `wp⟦e⟧ Q s₁ ... sₙ`, where `e` is the program.
  -- We call `s₁ ... sₙ` the excess state args; the backward rules need to account for these.
  -- Excess state args are introduced by the spec of `get` (see lambda case above).
  let excessArgs := args.drop 4
  let f := e.getAppFn

  trace[Elab.Tactic.Do.vcgen] "📜 Program: {e}"

  -- The four "program-shape" steps below all consume one unit of fuel
  -- (the `stepLimit` config option) when they make progress, so the calls to
  -- `VCGen.burnOne` are gathered here rather than scattered inside the helpers.

  -- Let-expressions: hoist to top of goal
  if let some r ← tryLetHoist goal head H σs ent args wpConst m ps instWP α e f then
    VCGen.burnOne
    return r

  -- Split ite/dite/match (or iota-reduce if discriminant is concrete)
  if let some r ← trySplit goal head H σs ent args wpConst m ps instWP α e excessArgs then
    VCGen.burnOne
    return r

  -- Zeta-unfold local let bindings on demand
  if let some r ← tryFvarZeta goal head H σs ent args wpConst m ps instWP α e f then
    VCGen.burnOne
    return r

  -- Apply registered specifications, or fall through to `.noStrategyForProgram`.
  VCGen.burnOne
  applySpec goal e excessArgs m σs ps instWP

end VCGen
