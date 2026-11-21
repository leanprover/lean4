/-
Copyright (c) 2026 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude
public import Init.Grind.Ring.Basic
import Init.ByCases
import Init.Omega

/-! Semifields and inverse identities that do not require subtraction. -/

@[expose] public section
namespace Lean.Grind

/-- A commutative semiring with inverses for nonzero elements. -/
class Semifield (α : Type u) extends CommSemiring α, Inv α, Div α where
  /-- Division is multiplication by the inverse. -/
  div_eq_mul_inv : ∀ a b : α, a / b = a * b⁻¹
  /-- A semifield is nontrivial. -/
  zero_ne_one : (0 : α) ≠ 1
  /-- The inverse of zero is zero. -/
  inv_zero : (0 : α)⁻¹ = 0
  /-- The inverse of a nonzero element is a right inverse. -/
  mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1

attribute [instance 100] Semifield.toInv Semifield.toDiv

namespace Semifield
variable [Semifield α]

theorem inv_mul_cancel {a : α} (h : a ≠ 0) : a⁻¹ * a = 1 := by
  rw [CommSemiring.mul_comm, mul_inv_cancel h]

theorem eq_inv_of_mul_eq_one {a b : α} (h : a * b = 1) : a = b⁻¹ := by
  by_cases hb : b = 0
  · subst hb
    rw [Semiring.mul_zero] at h
    exact False.elim (zero_ne_one h)
  · have := congrArg (fun x => x * b⁻¹) h
    simpa [Semiring.mul_assoc, mul_inv_cancel hb, Semiring.mul_one, Semiring.one_mul] using this

theorem inv_one : (1 : α)⁻¹ = 1 :=
  (eq_inv_of_mul_eq_one (Semiring.mul_one 1)).symm

theorem inv_inv (a : α) : a⁻¹⁻¹ = a := by
  by_cases h : a = 0
  · subst h; simp [inv_zero]
  · symm; exact eq_inv_of_mul_eq_one (mul_inv_cancel h)

theorem of_mul_eq_zero {a b : α} (h : a * b = 0) : a = 0 ∨ b = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  by_cases hb : b = 0
  · exact Or.inr hb
  have w := congrArg (fun x => x * b⁻¹ * a⁻¹) h
  rw [Semiring.mul_assoc a b, mul_inv_cancel hb, Semiring.mul_one, mul_inv_cancel ha,
    Semiring.zero_mul, Semiring.zero_mul] at w
  exact False.elim (zero_ne_one w.symm)

theorem inv_mul (a b : α) : (a * b)⁻¹ = a⁻¹ * b⁻¹ := by
  by_cases ha : a = 0
  · subst ha; simp [Semiring.zero_mul, inv_zero]
  by_cases hb : b = 0
  · subst hb; simp [Semiring.mul_zero, inv_zero]
  symm
  apply eq_inv_of_mul_eq_one
  rw [Semiring.mul_assoc, CommSemiring.mul_left_comm b⁻¹ a b,
    ← Semiring.mul_assoc a⁻¹ a, inv_mul_cancel ha, Semiring.one_mul, inv_mul_cancel hb]

theorem mul_mul_inv_cancel {a b c : α} (ha : a ≠ 0) :
    a * b * (c * a)⁻¹ = b * c⁻¹ := by
  rw [inv_mul, CommSemiring.mul_comm c⁻¹, ← Semiring.mul_assoc,
    Semiring.mul_assoc a b, CommSemiring.mul_comm b, ← Semiring.mul_assoc,
    mul_inv_cancel ha, Semiring.one_mul]

theorem inv_pow (a : α) (n : Nat) : (a ^ n)⁻¹ = a⁻¹ ^ n := by
  induction n with
  | zero => rw [Semiring.pow_zero, Semiring.pow_zero, inv_one]
  | succ n ih => rw [Semiring.pow_succ, Semiring.pow_succ, inv_mul, ih]

theorem of_pow_eq_zero (a : α) (n : Nat) : a ^ n = 0 → a = 0 := by
  induction n with
  | zero => simp [Semiring.pow_zero]; intro h; exact False.elim (zero_ne_one h.symm)
  | succ n ih =>
    rw [Semiring.pow_succ]
    intro h
    exact (of_mul_eq_zero h).elim ih id

attribute [local instance] Semiring.natCast in
theorem natCast_ne_zero [IsCharP α 0] {n : Nat} (h : n ≠ 0) : (n : α) ≠ 0 := by
  simpa [IsCharP.natCast_eq_zero_iff] using h

end Semifield
end Lean.Grind
