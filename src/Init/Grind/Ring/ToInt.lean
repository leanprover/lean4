/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind.Ring.Basic
public import Init.Grind.ToInt

public section

namespace Lean.Grind

/-- A `ToInt` instance on a semiring preserves powers if it preserves numerals and multiplication. -/
def ToInt.pow_of_semiring [Semiring α] [ToInt α I] [ToInt.OfNat α I] [ToInt.Mul α I]
    (h₁ : I.isFinite) : ToInt.Pow α I where
  toInt_pow x n := by
    induction n with
    | zero =>
      rw [Semiring.pow_zero, ToInt.OfNat.toInt_ofNat, Int.pow_zero]
      rfl
    | succ n ih =>
      rw [Semiring.pow_succ, ToInt.Mul.toInt_mul]
      conv => lhs; rw [← ToInt.wrap_toInt I x]
      rw [ih, ← I.wrap_mul h₁, Int.pow_succ]

end Lean.Grind
