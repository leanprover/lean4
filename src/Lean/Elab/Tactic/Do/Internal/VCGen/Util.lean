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
public import Lean.Meta.Sym.Simp.Telescope
public import Lean.Meta.Sym.Util

open Lean Meta Sym
open Std.Do

/-!
Generic `VCGenM` helpers: small-cap operations on `MVarId`s, telescope-aware
`simp` driver, hypothesis-internalization for grind, and a residual-goal
generalization of `applyRflAndAndIntro`. None of these know anything about
`SPred` entailment specifically.
-/

namespace Lean.Elab.Tactic.Do.Internal

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
      throwError m!"[mvcgen' +debug] BackwardRule {ruleDesc} failed to \
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

public def simpTargetTelescope (mvarId : MVarId) : VCGenM (MVarId × Bool) := do
  let some methods := (← read).hypSimpMethods | return (mvarId, false)
  let target ← mvarId.getType
  let simpState := (← get).simpState
  let methods := { methods with pre := Sym.Simp.simpTelescope }
  let (result, simpState') ← Sym.Simp.SimpM.run (Sym.Simp.simp target) methods {} simpState
  modify fun s => { s with simpState := simpState' }
  match result with
  | .rfl .. => return (mvarId, false)
  | .step newTarget proof .. =>
    let mvarId' ← mvarId.replaceTargetEq newTarget proof
    return (mvarId', true)

/--
Simplify the forall telescope of the target using `Sym.Simp.simpTelescope`,
then introduce all binders via `Sym.intros`.
-/
public def introsSimp (mvarId : MVarId) (errorMsg : MessageData) : VCGenM MVarId := do
  let (mvarId, progress) ← simpTargetTelescope mvarId
  match ← Sym.intros mvarId with
  | .failed =>
    if progress then
      return mvarId
    else
      throwError m!"Failed to intro on {mvarId}\nContext: {errorMsg}."
  | .goal _ mvarId' => return mvarId'

/--
Solves conjunctions whose leaves are `True` or `e₁ = e₂`, and returns a residual goal containing
exactly the conjuncts that could not be solved.
This procedure may assign metavariables in `e₁`/`e₂`, for example for `e = ?m` it will assign
`?m := e`.
-/
public partial def repeatAndRfl (goal : MVarId) : VCGenM (Option MVarId) :=
    goal.withContext do
  let ctx ← read
  let ty ← instantiateMVars (← goal.getType)
  if ty.isAppOf ``True then
    goal.assign (mkConst ``True.intro)
    return none
  else if ty.isAppOf ``And then
    let .goals [g₁, g₂] ← ctx.andIntroRule.applyChecked goal
      | throwError "repeatAndRfl: failed to apply {.ofConstName ``And.intro} to{indentExpr ty}"
    match ← repeatAndRfl g₁, ← repeatAndRfl g₂ with
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
    if ← withAssignableSyntheticOpaque <| isDefEqS lhs rhs then
      goal.assign (mkApp2 (mkConst ``Eq.refl [← Meta.getLevel ty]) ty lhs)
      return none
    else
      return some goal
  else
    return some goal

end VCGen
end Lean.Elab.Tactic.Do.Internal
