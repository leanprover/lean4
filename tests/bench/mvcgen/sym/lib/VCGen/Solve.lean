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

/--
The main VC generation step. Operates on a plain `MVarId` with no knowledge of grind.
Returns `.goals subgoals` when the goal was decomposed, or a classification result
(`.noEntailment`, `.noProgramFoundInTarget`, etc.) when no further decomposition is possible.

The function performs the following steps in order:

1. **Forall introduction**: If the target is a `∀`, introduce binders via `Sym.intros`.
2. **Triple unfolding**: If the target is `⦃P⦄ x ⦃Q⦄`, unfold into `P ⊢ₛ wp⟦x⟧ Q`.
3. **PostCond.entails decomposition**: Split `PostCond.entails` into its components.
4. **Lambda introduction**: If the RHS `T` in `H ⊢ₛ T` is a lambda, eta-expand via
   `SPred.entails_cons_intro` (introduces an extra state variable).
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
  trace[Elab.Tactic.Do.vcgen] "target: {target}"
  -- There are two layers of preprocessing before we get to taking apart program syntax.
  -- The first one is concerned with simplifying `target` until it is of the form `H ⊢ₛ T`.
  -- The second one is concerned with simplifying `H` and `T` such that none are head redexes
  -- and `T` is of the form `wp⟦e⟧ Q s₁ ... sₙ`.

  if target.isForall then
    return .goals [← introsSimp goal m!"foralls in `solve`"]

  if target.isLet then
    if isDuplicable target.letValue! then
      trace[Elab.Tactic.Do.vcgen] "let-zeta-dup: {target.letName!}"
      -- Zeta right away: substitute value into body with sharing
      let target' ← Sym.instantiateRevBetaS target.letBody! #[target.letValue!]
      return .goals [← goal.replaceTargetDefEq target']
    else
      trace[Elab.Tactic.Do.vcgen] "let-intro: {target.letName!}"
      -- Introduce let binding into the local context with proper sharing
      return .goals [← introsSimp goal m!"let-intro: {target.letName!}"]

  let f := target.getAppFn
  if f.isConstOf ``Triple then
    let goal ← tripleOfWP goal
    return .goals [goal]

  if let some goals ← solvePostCondEntails goal then
    return .goals goals

  let_expr ent@SPred.entails σs H T := target | return .noEntailment target
  -- The goal is of the form `H ⊢ₛ T`. Try some reductions to expose `wp⟦e⟧ Q s₁ ... sₙ` in `T`.

  if T.isLambda then
    -- This happens after applying the `get` spec. We have `T = (fun s => (wp⟦e⟧ Q, Q.snd).fst s s)`.
    -- Do what `mIntroForall` does, that is, eta-expand. Note that this introduces an
    -- extra state arg `s` to reduce away the lambda.
    let .goals [goal] ← (← read).entailsConsIntroRule.apply goal
      | throwError "Applying {.ofConstName ``SPred.entails_cons_intro} to {← goal.getType} failed. It should not."
    return .goals [goal]

  /-
  Do a very targeted simplification to turn `H ⊢ₛ (fun _ => T, Q.snd).fst s` into `H ⊢ₛ T`, and
  similarly for `H`.
  This often arises as follows during backward reasoning (i.e., in precondition VCs):
  ```
    H ⊢ₛ wp⟦get >>= set⟧ Q
  = H ⊢ₛ wp⟦get⟧ (fun a => wp⟦set a⟧ Q, Q.snd)
  = H ⊢ₛ (fun s => (fun a => wp⟦set a⟧ Q, Q.snd).fst s s)
  = H s ⊢ₛ (fun a => wp⟦set a⟧ Q, Q.snd).fst s s
  -- This is where we simplify!
  = H s ⊢ₛ wp⟦set s⟧ Q s
  = H s ⊢ₛ Q.fst s s
  ```
  Furthermore, redexes in `H` occur in postcondition VCs.
  -/
  let H? ← reduceHead? H
  let T? ← reduceHead? T
  if H?.isSome || T?.isSome then
    let goal ← goal.replaceTargetDefEq (← Sym.Internal.mkAppS₃ ent σs (H?.getD H) (T?.getD T))
    return .goals [goal]

  -- Look for program syntax in `T`.
  T.withApp fun head args => do

  unless head.isConstOf ``PredTrans.apply do
    -- The target is not a predicate transformer. We assume there is no weakest precondition to
    -- discharge and try solving by (syntactic) rfl.
    trace[Elab.Tactic.Do.vcgen] "Trying rfl {goal}"
    if ← withAssignableSyntheticOpaque <| isDefEqS H T then
      trace[Elab.Tactic.Do.vcgen] "Solved by rfl {goal}"
      goal.assign (mkApp2 (mkConst ``SPred.entails.refl ent.constLevels!) σs H)
      return .goals []
    if let some goal ← solveSPredEntails goal then
      return .goals [goal]
    return .noProgramFoundInTarget T

  let wp := args[2]!
  let_expr wpConst@WP.wp m ps instWP α e := wp | return .noProgramFoundInTarget T
  -- `T` is of the form `wp⟦e⟧ Q s₁ ... sₙ`, where `e` is the program.
  -- We call `s₁ ... sₙ` the excess state args; the backward rules need to account for these.
  -- Excess state args are introduced by the spec of `get` (see lambda case above).
  let excessArgs := args.drop 4
  let f := e.getAppFn
  withTraceNode `Elab.Tactic.Do.vcgen (msg := fun _ => return m!"Program: {e}") do

  -- Replace the program in the goal with `e'` (which must be definitionally equal).
  let replaceProgDefEq (e' : Expr) : VCGenM MVarId := do
    let wp ← Sym.Internal.mkAppS₅ wpConst m ps instWP α e'
    let T ← mkAppNS head (args.set! 2 wp)
    let target ← mkAppS₃ ent σs H T
    goal.replaceTargetDefEq target

  -- Let-expressions: hoist to top of goal
  if let .letE x ty val body nonDep := f then
    trace[Elab.Tactic.Do.vcgen] "let-hoist: {x}"
    let e' ← mkAppRevS body e.getAppRevArgs  -- body still has #0 for the let-bound var
    let wp' ← Sym.Internal.mkAppS₅ wpConst m ps instWP α e'
    let T' ← mkAppNS head (args.set! 2 wp')
    let target' ← mkAppS₃ ent σs H T'
    let hoisted := Expr.letE x ty val target' nonDep
    return .goals [← goal.replaceTargetDefEq hoisted]

  -- Split ite/dite/match
  if let some info ← liftMetaM <| Lean.Elab.Tactic.Do.getSplitInfo? e then
    -- Try iota reduction first (reduces matcher/recursor with concrete discriminant)
    if let some e' ← liftMetaM <| withReducible <| reduceRecMatcher? e then
      return .goals [← replaceProgDefEq (← shareCommonInc e')]
    let rule ← mkBackwardRuleFromSplitInfoCached info m σs ps instWP excessArgs
    let ApplyResult.goals goals ← rule.apply goal
      | throwError "Failed to apply split rule for {indentExpr e}"
    return .goals goals

  -- Zeta-unfold local let bindings on demand
  if let some fvarId := f.fvarId? then
    if let some val ← fvarId.getValue? then
      trace[Elab.Tactic.Do.vcgen] "fvar-zeta: {(← fvarId.getUserName)}"
      let e' ← shareCommonInc (val.betaRev e.getAppRevArgs)
      return .goals [← replaceProgDefEq e']

  -- Apply registered specifications (both triple and simp specs use cached backward rules).
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

end VCGen
