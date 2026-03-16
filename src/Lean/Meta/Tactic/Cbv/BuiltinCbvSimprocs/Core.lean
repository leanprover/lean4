/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wojciech Różowski
-/
module
prelude
import Lean.Meta.Sym.Simp.SimpM
import Init.Sym.Lemmas
import Init.CbvSimproc
import Lean.Meta.Tactic.Cbv.CbvSimproc

namespace Lean.Meta.Sym.Simp

/-- Short-circuit evaluation of `Or`. Simplifies only the left argument;
if it reduces to `True`, returns `True` immediately without evaluating the right side. -/
builtin_cbv_simproc ↓ simpOr (@Or _ _) := fun e => do
  let_expr Or a b := e | return .rfl
  match (← simp a) with
  | .rfl _ =>
    if (← isTrueExpr a) then
      return .step (← getTrueExpr) (mkApp (mkConst ``true_or) b) (done := true)
    else if (← isFalseExpr a) then
      return .step b (mkApp (mkConst ``false_or) b)
    else
      return .rfl
  | .step a' ha _ =>
    if (← isTrueExpr a') then
      return .step (← getTrueExpr) (mkApp (e.replaceFn ``Sym.or_eq_true_left) ha) (done := true)
    else if (← isFalseExpr a') then
      return .step b (mkApp (e.replaceFn ``Sym.or_eq_right) ha)
    else
      return .rfl

/-- Short-circuit evaluation of `And`. Simplifies only the left argument;
if it reduces to `False`, returns `False` immediately without evaluating the right side. -/
builtin_cbv_simproc ↓ simpAnd (@And _ _) := fun e => do
  let_expr And a b := e | return .rfl
  match (← simp a) with
  | .rfl _ =>
    if (← isFalseExpr a) then
      return .step (← getFalseExpr) (mkApp (mkConst ``false_and) b) (done := true)
    else if (← isTrueExpr a) then
      return .step b (mkApp (mkConst ``true_and) b)
    else
      return .rfl
  | .step a' ha _ =>
    if (← isFalseExpr a') then
      return .step (← getFalseExpr) (mkApp (e.replaceFn ``Sym.and_eq_false_left) ha) (done := true)
    else if (← isTrueExpr a') then
      return .step b (mkApp (e.replaceFn ``Sym.and_eq_left) ha)
    else
      return .rfl

end Lean.Meta.Sym.Simp
