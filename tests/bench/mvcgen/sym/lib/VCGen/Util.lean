/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Graf
-/
module
public import Lean.Meta
public meta import Lean.Meta
meta import Lean.Meta.Sym.Pattern
meta import Lean.Meta.Sym.Simp.DiscrTree
public meta import Lean.Meta.Tactic.Grind.Main
public meta import Lean.Meta.Tactic.Grind.Solve
public meta import VCGen.Context
public meta import VCGen.Reduce

open Lean Meta Sym
open Std.Do

/-!
Generic `VCGenM` helpers: small-cap operations on `MVarId`s, telescope-aware
`simp` driver, hypothesis-internalization for grind, and a residual-goal
generalization of `applyRflAndAndIntro`. None of these know anything about
`SPred` entailment specifically.
-/

@[inline]
public meta def _root_.Std.HashMap.getDM [Monad m] [BEq α] [Hashable α]
    (cache : Std.HashMap α β) (key : α) (fallback : m β) : m (β × Std.HashMap α β) := do
  if let some b := cache.get? key then
    return (b, cache)
  let b ← fallback
  return (b, cache.insert key b)

namespace VCGen

open Sym Sym.Internal

-- The following function is vendored until it is made public:
/-- `mkAppRevRangeS f b e args == mkAppRev f (revArgs.extract b e)` -/
public meta def mkAppRevRangeS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (beginIdx endIdx : Nat) (revArgs : Array Expr) : m Expr :=
  loop revArgs beginIdx f endIdx
where
  loop (revArgs : Array Expr) (start : Nat) (b : Expr) (i : Nat) : m Expr := do
  if i ≤ start then
    return b
  else
    let i := i - 1
    loop revArgs start (← mkAppS b revArgs[i]!) i

public meta def mkAppRevS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (revArgs : Array Expr) : m Expr :=
  mkAppRevRangeS f 0 revArgs.size revArgs

public meta def mkAppRangeS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (beginIdx endIdx : Nat) (args : Array Expr) : m Expr :=
  loop args endIdx f beginIdx
where
  loop (args : Array Expr) (end' : Nat) (b : Expr) (i : Nat) : m Expr := do
  if end' ≤ i then
    return b
  else
    loop args end' (← mkAppS b args[i]!) (i + 1)

public meta def mkAppNS [Monad m] [Internal.MonadShareCommon m] (f : Expr) (args : Array Expr) : m Expr :=
  mkAppRangeS f 0 args.size args

public meta def simpTargetTelescope (mvarId : MVarId) : VCGenM (MVarId × Bool) := do
  let some methods := (← read).hypSimpMethods | return (mvarId, false)
  let target ← mvarId.getType
  let simpState := (← get).simpState
  let methods := { methods with pre := Sym.Simp.simpTelescope }
  let (result, simpState') ← Sym.Simp.SimpM.run (Sym.Simp.simp target) methods {} simpState
  modify fun s => { s with simpState := simpState' }
  let mvarId ← match result with
    | .rfl .. => pure (mvarId, false)
    | .step newTarget proof .. => pure (← mvarId.replaceTargetEq newTarget proof, true)

/--
Simplify the forall telescope of the target using `Sym.Simp.simpTelescope`,
then introduce all binders via `Sym.intros`.
-/
public meta def introsSimp (mvarId : MVarId) (errorMsg : MessageData) : VCGenM MVarId := do
  let (mvarId, progress) ← simpTargetTelescope mvarId
  match ← Sym.intros mvarId with
  | .failed =>
    if progress then
      return mvarId
    else
      throwError m!"Failed to intro on {mvarId}\nContext: {errorMsg}."
  | .goal _ mvarId' =>
    return mvarId'

/-- Internalize pending hypotheses into the E-graph for sharing before forking to multiple subgoals.
If `processHypotheses` discovers a contradiction (`inconsistent = true`), the E-graph state
contains stale proof data (the contradiction proof targets the parent's mvar, not the children's).
In that case, restore the pre-internalization state so each child can discover the contradiction
independently and construct its own proof via `closeGoal`.
-/
public meta def PreTac.processHypotheses (preTac : PreTac) (goal : Grind.Goal) : VCGenM Grind.Goal := do
  if preTac.isGrind then
    Grind.processHypotheses goal
  else
    return goal

/--
Solves conjunctions whose leaves are `True` or `e₁ = e₂`, and returns a residual goal containing
exactly the conjuncts that could not be solved.
This procedure may assign metavariables in `e₁`/`e₂`, for example for `e = ?m` it will assign
`?m := e`.
-/
public meta partial def repeatAndRfl (goal : MVarId) : VCGenM (Option MVarId) :=
    goal.withContext do
  let ctx ← read
  let ty ← instantiateMVars (← goal.getType)
  if ty.isAppOf ``True then
    goal.assign (mkConst ``True.intro)
    return none
  else if ty.isAppOf ``And then
    let .goals [g₁, g₂] ← ctx.andIntroRule.apply goal
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
