/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module

prelude
public import Lean.Meta.Tactic.Grind.Main
public import Lean.Elab.Tactic.Do.Internal.VCGen.Context
public import Lean.Elab.Tactic.Do.Internal.VCGen.Reduce
public import Lean.Meta.Sym.AlphaShareBuilder
public import Lean.Meta.Sym.Intro
public import Lean.Meta.Sym.Simp.Goal
public import Lean.Meta.Sym.Simp.Telescope
public import Lean.Meta.Sym.Util

open Lean Meta Sym Lean.Order

/-!
Generic `VCGenM` helpers: checked backward-rule application, telescope-aware `simp` driver,
hygienic binder introduction, hypothesis-internalization for grind, and the trivial-conjunct
collapser `solveTrivialConjuncts`. None of these know anything about the entailment shapes `solve`
decomposes.
-/

namespace Lean.Elab.Tactic.Do.Internal

/-- Internalize a backward rule's pattern into the current `SymM` share table. See
`Pattern.shareCommon`. Designed for dot notation: `rule.shareCommon`. -/
public def _root_.Lean.Meta.Sym.BackwardRule.shareCommon (rule : BackwardRule) : SymM BackwardRule :=
  return { rule with pattern := ← rule.pattern.shareCommon }

/--
`VCGenM` wrapper around `BackwardRule.apply`. Behaves identically to
`rule.apply goal` unless the application fails and `Context.debug` is on.
In that case it retries on a fresh metavariable whose type is the
`unfoldReducible`-normalized goal type. If the retry succeeds, an earlier
step forgot a normalization; we throw a hard error pointing at the rule and
the missing reduction.

`ruleDesc?` describes the rule for debug output. When `none`, the description
is reconstructed from `rule.expr.getAppFn` — works for the common case of a
constant rule. Pass a custom message for dynamically-built rules.

Designed for dot notation: `rule.applyChecked goal`. Requires
`open Lean.Elab.Tactic.Do.Internal` in scope so that the dot lookup resolves.
-/
public def Lean.Meta.Sym.BackwardRule.applyChecked (rule : BackwardRule) (goal : MVarId)
    (ruleDesc? : Option MessageData := none) : VCGenM ApplyResult := do
  let r ← rule.apply goal
  match r with
  | .goals _ => return r
  | .failed =>
    unless (← read).debug do return r
    let originalType ← goal.getType
    let normalized ← unfoldReducible originalType
    if normalized == originalType then return r
    let succeeded ← Lean.Meta.withoutModifyingMCtx do
      let goal' ← Meta.mkFreshExprSyntheticOpaqueMVar normalized
      match ← rule.apply goal'.mvarId! with
      | .goals _ => return true
      | .failed => return false
    if succeeded then
      let ruleDesc := ruleDesc?.getD <|
        match rule.expr.getAppFn with
        | .const declName _ => m!"`{.ofConstName declName}`"
        | _ => m!"<rule constructed from expression>"
      throwError m!"[vcgen +debug] BackwardRule {ruleDesc} failed to \
        apply to:{indentExpr originalType}\nbut succeeded after `unfoldReducible`-\
        normalization to:{indentExpr normalized}\nAn earlier step is missing a normalization. \
        Re-run with `set_option pp.all true` to see the structural difference."
    return r

namespace VCGen

open Sym Sym.Internal
open Lean.Elab.Tactic.Do.Internal

/-- `Grind.processHypotheses` if `Context.internalize` is `true`, otherwise a no-op. -/
public def processHypotheses (goal : Grind.Goal) : VCGenM Grind.Goal := do
  if (← read).internalize then Grind.processHypotheses goal else return goal

/--
Introduce all leading binders of `goal` in one pass, naming the `i`-th binder `overrides[i]` when
given and the binder's own name otherwise. Accessibility is decided by `tactic.hygienic` via
`mkFreshBinderNameForTactic`. The introduction itself is a single `Sym.intros` call (which keeps
the memoized, sharing-correct intro); only the names are chosen here. Returns the goal unchanged
when there are no leading binders.
-/
public def introsHygienic (goal : MVarId) (overrides : Array Name := #[]) : VCGenM MVarId :=
  goal.withContext do
    let rec collectBinders (type : Expr) (acc : Array Name) : Array Name :=
      match type with
      | .forallE n _ b _ => collectBinders b (acc.push n)
      | .letE n _ _ b _ => collectBinders b (acc.push n)
      | _ => acc
    let binderNames := collectBinders (← goal.getType) #[]
    if binderNames.isEmpty then return goal
    let mut names := #[]
    for h : i in *...binderNames.size do
      names := names.push (← Meta.mkFreshBinderNameForTactic (overrides[i]?.getD binderNames[i]))
    let .goal _ goal ← Sym.intros goal names | return goal
    return goal

/--
Simplify the goal's target with the configured hypothesis simp methods (a no-op without
`Context.hypSimpMethods`), threading the persistent simp cache through `VCGenM`'s state.
`.noProgress` is forwarded to the caller.
-/
public def simpGoalTelescope (goal : MVarId) : VCGenM Sym.SimpGoalResult := do
  let some methods := (← read).hypSimpMethods | return .noProgress
  let methods := { methods with pre := Sym.Simp.simpTelescope }
  let target ← goal.getType
  let (result, simpState') ← Sym.Simp.SimpM.run (Sym.Simp.simp target) methods {} (← get).simpState
  modify fun s => { s with simpState := simpState' }
  result.toSimpGoalResult goal

/--
Introduce the excess state arguments of an entailment goal `pre ⊑ rhs` whose lattice type is a
function type `σ₁ → … → σₙ → α`: repeatedly apply `stateArgIntro` (a backward rule for
`Lean.Order.le_of_forall_le`) and introduce the new state binder, until the lattice type is
no longer a function type. Returns `none` when the carrier is not a function type (nothing to
introduce); throws when the carrier is a function type that `le_of_forall_le` cannot peel, such as a
dependent function lattice `(a : α) → β a → …`.
-/
public partial def introsExcessArgs (goal : MVarId) :
    VCGenM (Option MVarId) := goal.withContext do
  let type ← goal.getType
  let_expr PartialOrder.rel α _inst _pre _rhs := type | return none
  unless α.isForall do return none
  let .goals [goal] ← (← read).backwardRules.stateArgIntro.applyChecked goal
    | throwError "failed to apply {.ofConstName ``Lean.Order.le_of_forall_le} to goal{indentExpr type}"
  let goal ← introsHygienic goal
  return (← introsExcessArgs goal) <|> some goal

/--
Solves conjunctions whose leaves are `True` or `e₁ = e₂`, and returns a residual goal containing
exactly the conjuncts that could not be solved.
This procedure may assign metavariables in `e₁`/`e₂`, for example for `e = ?m` it will assign
`?m := e`.
-/
public partial def solveTrivialConjuncts (goal : MVarId) : VCGenM (Option MVarId) :=
    goal.withContext do
  let ctx ← read
  let ty ← instantiateMVars (← goal.getType)
  if ty.isAppOf ``True then
    goal.assign (mkConst ``True.intro)
    return none
  else if ty.isAppOf ``And then
    let .goals [g₁, g₂] ← ctx.backwardRules.andIntro.applyChecked goal
      | throwError "solveTrivialConjuncts: failed to apply {.ofConstName ``And.intro} to{indentExpr ty}"
    match ← solveTrivialConjuncts g₁, ← solveTrivialConjuncts g₂ with
    | none,    none    => return none
    | some g,  none    => return some g
    | none,    some g  => return some g
    | some g₁', some g₂' =>
      let t₁ ← g₁'.getType
      let t₂ ← g₂'.getType
      let combined ← mkFreshExprSyntheticOpaqueMVar (mkApp2 (mkConst ``And) t₁ t₂)
      g₁'.assign (mkApp3 (mkConst ``And.left) t₁ t₂ combined)
      g₂'.assign (mkApp3 (mkConst ``And.right) t₁ t₂ combined)
      return some combined.mvarId!
  else if let some (ty, lhs, rhs) := ty.app3? ``Eq then
    let lhs ← reduceHead lhs
    let rhs ← reduceHead rhs
    let u ← Meta.getLevel ty
    let goal ← goal.replaceTargetDefEq (mkApp3 (mkConst ``Eq [u]) ty lhs rhs)
    -- Synthetic opaque metavariables (e.g. invariant holes) stay rigid; natural
    -- metavariables may be assigned (e.g. `?m := e` for `e = ?m` leaves).
    if ← isDefEqS lhs rhs then
      goal.assign (mkApp2 (mkConst ``Eq.refl [← Meta.getLevel ty]) ty lhs)
      return none
    else
      return some goal
  else
    return some goal

end VCGen
end Lean.Elab.Tactic.Do.Internal
