/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Zero

/-!
# A monolithic commutative ring typeclass for internal use in `grind`.
-/

namespace Lean.Grind

class CommRing (α : Type u) extends Add α, Zero α, Mul α, One α, Neg α where
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a : α, a + 0 = a
  neg_add_cancel : ∀ a : α, -a + a = 0
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  mul_one : ∀ a : α, a * 1 = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  zero_mul : ∀ a : α, 0 * a = 0

namespace CommRing

variable {α : Type u} [CommRing α]

theorem zero_add (a : α) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem add_neg_cancel (a : α) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

theorem one_mul (a : α) : 1 * a = a := by
  rw [mul_comm, mul_one]

theorem right_distrib (a b c : α) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c, mul_comm c]

theorem mul_zero (a : α) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

end CommRing

end Lean.Grind
