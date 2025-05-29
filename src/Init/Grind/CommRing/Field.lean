/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.CommRing.Basic

namespace Lean.Grind

class Field (α : Type u) extends CommRing α, Inv α, Div α where
  div_eq_mul_inv : ∀ a b : α, a / b = a * b⁻¹
  inv_zero : (0 : α)⁻¹ = 0
  inv_one : (1 : α)⁻¹ = 1
  mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1

attribute [instance 100] Field.toInv Field.toDiv

namespace Field

variable [Field α] {a : α}

theorem inv_mul_cancel (h : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [CommSemiring.mul_comm, mul_inv_cancel h]

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
