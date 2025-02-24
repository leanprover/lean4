/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Lean.Meta.AppBuilder
import Lean.Meta.MatchUtil

namespace Lean.Meta.Grind
/-! A basic "equality resolution" procedure. -/

/--
Similar to `forallMetaTelescopeReducing`, but if `prop` resulting type is of the form `¬ p`, it will "convert" it so `p → False`, and
will return a hypothesis for it and return `False` as the resulting type.
-/
private def forallMetaTelescopeReducingAndUnfoldingNot (prop : Expr) : MetaM (Array Expr × Expr) := do
  let (ms, _, type) ← forallMetaTelescopeReducing prop
  if let some p ← matchNot? type then
    let m ← mkFreshExprMVar p
    return (ms.push m, mkConst ``False)
  return (ms, type)

private def eqResCore (prop proof : Expr) : MetaM (Option (Expr × Expr)) := withNewMCtxDepth do
  /-
  We use `forallMetaTelescopeReducingAndUnfoldingNot` because we want to treat
  ```
  ∀ x, ¬ f x = f a
  ```
  as
  ```
  ∀ x, f x = f a → False
  ```
  recall that `¬` is not reducible.
  -/
  let (ms, type) ← forallMetaTelescopeReducingAndUnfoldingNot prop
  if ms.isEmpty then return none
  let mut progress := false
  for m in ms do
    let type ← inferType m
    let_expr Eq _ lhs rhs ← type
      | pure ()
    if (← isDefEq lhs rhs) then
      unless (← m.mvarId!.checkedAssign (← mkEqRefl lhs)) do
        return none
      progress := true
  unless progress do
    return none
  if (← ms.anyM fun m => m.mvarId!.isDelayedAssigned) then
    return none
  let prop' ← instantiateMVars type
  let proof' ← instantiateMVars (mkAppN proof ms)
  let ms ← ms.filterM fun m => return !(← m.mvarId!.isAssigned)
  let prop' ← mkForallFVars ms prop' (binderInfoForMVars := .default)
  let proof' ← mkLambdaFVars ms proof'
  return some (prop', proof')

/--
A basic "equality resolution" procedure: Given a proposition `prop` with a proof `proof`, it attempts to resolve equality hypotheses using `isDefEq`. For example, it reduces `∀ x y, f x = f (g y y) → g x y = y` to `∀ y, g (g y y) y = y`, and `∀ (x : Nat), f x ≠ f a` to `False`.
If successful, the result is a pair `(prop', proof)`, where `prop'` is the simplified proposition,
and `proof : prop → prop'`
-/
def eqResolution (prop : Expr) : MetaM (Option (Expr × Expr)) :=
  withLocalDeclD `h prop fun h => do
    let some (prop', proof') ← eqResCore prop h
      | return none
    let proof' ← mkLambdaFVars #[h] proof'
    return some (prop', proof')

end Lean.Meta.Grind
