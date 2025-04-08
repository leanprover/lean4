/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Zero
import Init.Data.Int.DivMod.Lemmas
import Init.TacticsExtra

/-!
# A monolithic commutative ring typeclass for internal use in `grind`.
-/

namespace Lean.Grind

class CommRing (α : Type u) extends Add α, Zero α, Mul α, One α, Neg α, IntCast α where
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a : α, a + 0 = a
  neg_add_cancel : ∀ a : α, -a + a = 0
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  mul_one : ∀ a : α, a * 1 = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  zero_mul : ∀ a : α, 0 * a = 0
  cast_zero : ((0 : Int) : α) = (0 : α) := by rfl
  cast_one : ((1 : Int) : α) = (1 : α) := by rfl
  cast_add : ∀ a b : Int, ((a + b : Int) : α) = (a : α) + (b : α) := by intros; rfl
  cast_mul : ∀ a b : Int, ((a * b : Int) : α) = (a : α) * (b : α) := by intros; rfl
  cast_neg : ∀ a : Int, ((-a : Int) : α) = -(a : α) := by intros; rfl
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

theorem cast_sub (a b : Int) : ((a - b : Int) : α) = (a : α) + -(b : α) := by
  rw [Int.sub_eq_add_neg, cast_add, cast_neg]

end CommRing

open CommRing

class IsCharP (α : Type u) [CommRing α] (p : outParam Nat) where
  char (p) : ∀ {x : Int}, (x : α) = 0 ↔ x % p = 0

namespace IsCharP

variable {α : Type u} [CommRing α] [IsCharP α p]

theorem ext_iff {x y : Int} : (x : α) = (y : α) ↔ x % p = y % p := by
  constructor
  · intro h
    replace h : ((x - y : Int) : α) = 0 := by rw [cast_sub, h, add_neg_cancel]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr ((IsCharP.char p).mp h)
  · intro h
    have : ((x - y : Int) : α) = 0 :=
      (IsCharP.char p).mpr (by rw [Int.sub_emod, h, Int.sub_self, Int.zero_emod])
    replace this := congrArg (· + (y : α)) this
    simpa [cast_sub, zero_add, add_assoc, neg_add_cancel, add_zero] using this

theorem ext {x y : Int} (h : x % p = y % p) : (x : α) = (y : α) := ext_iff.mpr h

theorem cast_emod (x : Int) : ((x % p : Int) : α) = (x : α) := by
  rw [ext_iff, Int.emod_emod]

theorem eq_zero_iff_of_lt {x : Int} (h₁ : 0 ≤ x) (h₂ : x < p) : (x : α) = 0 ↔ x = 0 := by
  rw [IsCharP.char, Int.emod_eq_of_lt h₁ h₂]

theorem eq_iff_of_lt {x y : Int} (h₁ : 0 ≤ x) (h₂ : x < p) (h₃ : 0 ≤ y) (h₄ : y < p) :
    (x : α) = (y : α) ↔ x = y := by
  rw [ext_iff, Int.emod_eq_of_lt h₁ h₂, Int.emod_eq_of_lt h₃ h₄]

end IsCharP

end Lean.Grind
