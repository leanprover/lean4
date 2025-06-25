/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.Ring.Basic
import Init.Grind.ToInt

namespace Lean.Grind

/-- A `ToInt` instance on a semiring preserves powers if it preserves numerals and multiplication. -/
def ToInt.pow_of_semiring [Semiring α] [ToInt α I] [ToInt.OfNat α I] [ToInt.Mul α I]
    (h₁ : I.isFinite) (h₂ : 1 ∈ I) : ToInt.Pow α I where
  toInt_pow x n := by
    induction n with
    | zero =>
      rw [Semiring.pow_zero]
      rw [ToInt.OfNat.toInt_ofNat _ h₂]
      rw [Int.pow_zero]
      rw [(I.wrap_eq_self_iff (IntInterval.nonEmpty_of_mem h₂) _).mpr h₂]
      rfl
    | succ n ih =>
      rw [Semiring.pow_succ]
      rw [ToInt.Mul.toInt_mul]
      conv => lhs; rw [← ToInt.wrap_toInt I x]
      rw [ih]
      rw [← I.wrap_mul h₁]
      rw [Int.pow_succ]

end Lean.Grind
