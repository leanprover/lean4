/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind.Ring.Basic

public section

namespace Lean.Grind

/--
A field is a commutative ring with inverses for all non-zero elements.
-/
class Field (α : Type u) extends CommRing α, Inv α, Div α where
  /-- Division is multiplication by the inverse. -/
  div_eq_mul_inv : ∀ a b : α, a / b = a * b⁻¹
  /-- Zero is not equal to one: fields are non trivial.-/
  zero_ne_one : (0 : α) ≠ 1
  /-- The inverse of zero is zero. This is a "junk value" convention. -/
  inv_zero : (0 : α)⁻¹ = 0
  /-- The inverse of a non-zero element is a right inverse. -/
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
    simp [Field.inv_zero, AddCommGroup.neg_zero]
  · symm
    apply eq_inv_of_mul_eq_one
    simp [Ring.neg_mul, Ring.mul_neg, AddCommGroup.neg_neg, Field.inv_mul_cancel h]

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

theorem of_mul_eq_zero {a b : α} : a*b = 0 → a = 0 ∨ b = 0 := by
  cases (Classical.em (a = 0)); simp [*, Semiring.zero_mul]
  cases (Classical.em (b = 0)); simp [*, Semiring.mul_zero]
  next h₁ h₂ =>
  replace h₁ := Field.mul_inv_cancel h₁
  replace h₂ := Field.mul_inv_cancel h₂
  intro h
  replace h := congrArg (· * b⁻¹ * a⁻¹) h; simp [Semiring.zero_mul] at h
  rw [Semiring.mul_assoc, Semiring.mul_assoc, ← Semiring.mul_assoc b, h₂, Semiring.one_mul, h₁] at h
  have := Field.zero_ne_one (α := α)
  simp [h] at this

theorem mul_inv (a b : α) : (a*b)⁻¹ = a⁻¹*b⁻¹ := by
  cases (Classical.em (a = 0)); simp [*, Semiring.zero_mul, Field.inv_zero]
  cases (Classical.em (b = 0)); simp [*, Semiring.mul_zero, Field.inv_zero]
  cases (Classical.em (a*b = 0)); simp [*, Field.inv_zero]
  next h => cases (of_mul_eq_zero h) <;> contradiction
  next h₁ h₂ h₃ =>
    replace h₁ := Field.inv_mul_cancel h₁
    replace h₂ := Field.inv_mul_cancel h₂
    replace h₃ := Field.mul_inv_cancel h₃
    replace h₃ := congrArg (b⁻¹*a⁻¹* ·) h₃; simp at h₃
    rw [Semiring.mul_assoc, Semiring.mul_assoc, ← Semiring.mul_assoc (a⁻¹), h₁, Semiring.one_mul,
      ← Semiring.mul_assoc, h₂, Semiring.one_mul, Semiring.mul_one, CommRing.mul_comm (b⁻¹)] at h₃
    assumption

theorem of_pow_eq_zero (a : α) (n : Nat) : a^n = 0 → a = 0 := by
  induction n
  next => simp [Semiring.pow_zero]; intro h; have := zero_ne_one (α := α); exfalso; exact this h.symm
  next n ih =>
    simp [Semiring.pow_succ]; intro h
    apply Classical.byContradiction
    intro hne
    have := Field.mul_inv_cancel hne
    replace h := congrArg (· * a⁻¹) h; simp at h
    rw [Semiring.mul_assoc, this, Semiring.mul_one, Semiring.zero_mul] at h
    have := ih h
    contradiction

instance [IsCharP α 0] : NoNatZeroDivisors α := NoNatZeroDivisors.mk' <| by
  intro a b h w
  have := IsCharP.natCast_eq_zero_iff (α := α) 0 a
  simp only [Nat.mod_zero, h, iff_false] at this
  if h : b = 0 then
    exact h
  else
    rw [Semiring.ofNat_eq_natCast] at w
    replace w := congrArg (fun x => x * b⁻¹) w
    dsimp only [] at w
    rw [Semiring.nsmul_eq_ofNat_mul, Semiring.mul_assoc, Field.mul_inv_cancel h, Semiring.mul_one,
      Semiring.natCast_zero, Semiring.zero_mul, Semiring.ofNat_eq_natCast] at w
    contradiction

end Field

end Lean.Grind
