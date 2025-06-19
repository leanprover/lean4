/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.Ring.Basic

namespace Lean.Grind

class Field (α : Type u) extends CommRing α, Inv α, Div α where
  div_eq_mul_inv : ∀ a b : α, a / b = a * b⁻¹
  zero_ne_one : (0 : α) ≠ 1
  inv_zero : (0 : α)⁻¹ = 0
  mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1

attribute [instance 100] Field.toInv Field.toDiv

namespace Field

variable [Field α] {a : α}

theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [CommSemiring.mul_comm, mul_inv_cancel h]

theorem eq_inv_of_mul_eq_one (h : a * b = 1) : a = b⁻¹ := by
  by_cases h' : b = 0
  · subst h'
    rw [Semiring.mul_zero] at h
    exfalso
    exact zero_ne_one h
  · replace h := congrArg (fun x => x * b⁻¹) h
    simpa [Semiring.mul_assoc, mul_inv_cancel h', Semiring.mul_one, Semiring.one_mul] using h

theorem inv_one : (1 : α)⁻¹ = 1 :=
  (eq_inv_of_mul_eq_one (Semiring.mul_one 1)).symm

theorem inv_inv (a : α) : a⁻¹⁻¹ = a := by
  by_cases h : a = 0
  · subst h
    simp [Field.inv_zero]
  · symm
    apply eq_inv_of_mul_eq_one
    exact mul_inv_cancel h

theorem inv_neg (a : α) : (-a)⁻¹ = -a⁻¹ := by
  by_cases h : a = 0
  · subst h
    simp [Field.inv_zero, Ring.neg_zero]
  · symm
    apply eq_inv_of_mul_eq_one
    simp [Ring.neg_mul, Ring.mul_neg, Ring.neg_neg, Field.inv_mul_cancel h]

theorem inv_eq_zero_iff {a : α} : a⁻¹ = 0 ↔ a = 0 := by
  constructor
  · intro w
    by_cases h : a = 0
    · subst h
      rfl
    · have := congrArg (fun x => x * a) w
      dsimp at this
      rw [Semiring.zero_mul, inv_mul_cancel h] at this
      exfalso
      exact zero_ne_one this.symm
  · intro w
    subst w
    simp [Field.inv_zero]

theorem zero_eq_inv_iff {a : α} : 0 = a⁻¹ ↔ 0 = a := by
  rw [eq_comm, inv_eq_zero_iff, eq_comm]

instance [IsCharP α 0] : NoNatZeroDivisors α where
  no_nat_zero_divisors := by
    intro a b h w
    have := IsCharP.natCast_eq_zero_iff (α := α) 0 a
    simp only [Nat.mod_zero, h, iff_false] at this
    if h : b = 0 then
      exact h
    else
      rw [Semiring.ofNat_eq_natCast] at w
      replace w := congrArg (fun x => x * b⁻¹) w
      dsimp only [] at w
      rw [Semiring.hmul_eq_ofNat_mul, Semiring.mul_assoc, Field.mul_inv_cancel h, Semiring.mul_one,
        Semiring.natCast_zero, Semiring.zero_mul, Semiring.ofNat_eq_natCast] at w
      contradiction

end Field

end Lean.Grind
