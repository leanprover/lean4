/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind.Ring.Basic
public import Init.Data.Nat.Div.Basic
import Init.ByCases
import Init.Omega
import Init.RCases
import Init.TacticsExtra

public section

namespace Lean.Grind

/--
A field is a commutative ring with inverses for all non-zero elements.
-/
class Field (α : Type u) extends CommRing α, Inv α, Div α where
  /-- An exponentiation operator. -/
  [zpow : HPow α Int α]
  /-- Division is multiplication by the inverse. -/
  div_eq_mul_inv : ∀ a b : α, a / b = a * b⁻¹
  /-- Zero is not equal to one: fields are non trivial.-/
  zero_ne_one : (0 : α) ≠ 1
  /-- The inverse of zero is zero. This is a "junk value" convention. -/
  inv_zero : (0 : α)⁻¹ = 0
  /-- The inverse of a non-zero element is a right inverse. -/
  mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1
  /-- The zeroth power of any element is one. -/
  zpow_zero : ∀ a : α, a ^ (0 : Int) = 1
  /-- The (n+1)-st power of any element is the element multiplied by the n-th power. -/
  zpow_succ : ∀ (a : α) (n : Nat), a ^ (n + 1 : Int) = a ^ (n : Int) * a
  /-- Raising to a negative power is the inverse of raising to the positive power. -/
  zpow_neg : ∀ (a : α) (n : Int), a ^ (-n) = (a ^ n)⁻¹

attribute [implicit_reducible] Field.zpow
attribute [instance 100] Field.toInv Field.toDiv Field.zpow

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

theorem inv_eq_iff_eq_iff (a b : α) : a⁻¹ = b ↔ a = b⁻¹ := by
  constructor
  · intro h
    rw [← h, inv_inv]
  · intro h
    rw [h, inv_inv]

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

theorem of_mul_eq_zero {a b : α} : a * b = 0 → a = 0 ∨ b = 0 := by
  cases (Classical.em (a = 0)); · simp [*, Semiring.zero_mul]
  cases (Classical.em (b = 0)); · simp [*, Semiring.mul_zero]
  rename_i h₁ h₂
  replace h₁ := Field.mul_inv_cancel h₁
  replace h₂ := Field.mul_inv_cancel h₂
  intro h
  replace h := congrArg (· * b⁻¹ * a⁻¹) h; simp [Semiring.zero_mul] at h
  rw [Semiring.mul_assoc, Semiring.mul_assoc, ← Semiring.mul_assoc b, h₂, Semiring.one_mul, h₁] at h
  have := Field.zero_ne_one (α := α)
  simp [h] at this

theorem inv_mul (a b : α) : (a*b)⁻¹ = a⁻¹*b⁻¹ := by
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

theorem zpow_natCast (a : α) (n : Nat) : a ^ (n : Int) = a ^ n := by
  induction n
  next => simp [zpow_zero, Semiring.pow_zero]
  next n ih => rw [Int.natCast_add_one, zpow_succ, ih, Semiring.pow_succ]

theorem zpow_one (a : α) : a ^ (1 : Int) = a := by
  have : (1 : Int) = 0 + 1 := rfl
  rw [this, ← Int.natCast_zero, zpow_succ, Int.natCast_zero, zpow_zero, Semiring.one_mul]

theorem zpow_neg_one (a : α) : a ^ (-1) = a⁻¹ := by
  rw [zpow_neg, zpow_one]

theorem zpow_add_one {a : α} (h : a ≠ 0) (n : Int) : a ^ (n + 1) = a ^ n * a := by
  match n with
  | (n : Nat) => rw [zpow_succ, zpow_natCast]
  | -(n + 1 : Nat) =>
    rw [zpow_neg, Int.natCast_add, Int.cast_ofNat_Int, Int.neg_add, Int.neg_add_cancel_right,
      zpow_neg, zpow_succ, inv_mul, Semiring.mul_assoc, inv_mul_cancel h, Semiring.mul_one]

theorem zpow_sub_one {a : α} (h : a ≠ 0) (n : Int) : a ^ (n - 1) = a ^ n * a⁻¹ := by
  have h₁ := zpow_add_one h (-n)
  have h₂ : -n + 1 = - (n - 1) := by omega
  rw [h₂, zpow_neg, inv_eq_iff_eq_iff] at h₁
  rw [h₁, inv_mul, zpow_neg, inv_inv]

theorem zpow_add {a : α} (h : a ≠ 0) (m n : Int) : a ^ (m + n) = a ^ m * a ^ n := by
  match n with
  | (n : Nat) =>
    induction n with
    | zero => simp [zpow_zero, Semiring.mul_one]
    | succ n ih => rw [Int.natCast_add_one, zpow_succ, ← Int.add_assoc, zpow_add_one h, ih, Semiring.mul_assoc]
  | -(n + 1 : Nat) =>
    induction n with
    | zero => simp [Int.add_neg_one, zpow_sub_one h, zpow_neg_one]
    | succ n ih => rw [Int.natCast_add_one, Int.neg_add, Int.add_neg_one, ← Int.add_sub_assoc, zpow_sub_one h, zpow_sub_one h, ih, Semiring.mul_assoc]

theorem div_zero {x : α} : x / 0 = 0 := by rw [div_eq_mul_inv, inv_zero, Semiring.mul_zero]

theorem mul_div {x y z : α} : x * (y / z) = (x * y) / z := by
  rw [div_eq_mul_inv, div_eq_mul_inv, Semiring.mul_assoc]
theorem div_mul {x y z : α} : x / y * z = x * z / y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, Semiring.mul_assoc, CommSemiring.mul_comm y⁻¹,
    Semiring.mul_assoc]
theorem div_add {x y z : α} (hy : y ≠ 0) : x / y + z = (x + y * z) / y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, Semiring.right_distrib, CommSemiring.mul_comm y,
    Semiring.mul_assoc, Field.mul_inv_cancel hy, Semiring.mul_one]
theorem add_div {x y z : α} (hz : z ≠ 0) : x + y / z = (x * z + y) / z := by
  rw [div_eq_mul_inv, div_eq_mul_inv, Semiring.right_distrib, Semiring.mul_assoc,
    Field.mul_inv_cancel hz, Semiring.mul_one]

theorem div_div_right {x y z : α} : x / (y / z) = x * z / y := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, inv_mul, inv_inv, CommSemiring.mul_comm y⁻¹,
    Semiring.mul_assoc]
theorem div_div_left {x y z : α} : (x / y) / z = x / (y * z) := by
  rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, inv_mul, Semiring.mul_assoc]
theorem div_mul_cancel {x y : α} (h : y ≠ 0) : x / y * y = x := by
  rw [div_eq_mul_inv, Semiring.mul_assoc, Field.inv_mul_cancel h, Semiring.mul_one]

attribute [local instance] Semiring.natCast in
theorem natCast_ne_zero [IsCharP α 0] {n : Nat} (h : n ≠ 0) : (n : α) ≠ 0 := by
    simpa [IsCharP.natCast_eq_zero_iff]

attribute [local instance] Ring.intCast in
theorem intCast_div_of_dvd {x y : Int} (h : y ∣ x) (w : (y : α) ≠ 0) :
    ((x / y : Int) : α) = ((x : α) / (y : α)) := by
  obtain ⟨z, rfl⟩ := h
  by_cases hy : y = 0
  · simp_all [Ring.intCast_zero]
  · rw [Int.mul_ediv_cancel_left _ hy]
    rw [Ring.intCast_mul, CommSemiring.mul_comm, div_eq_mul_inv, Semiring.mul_assoc,
      mul_inv_cancel w, Semiring.mul_one]

attribute [local instance] Semiring.natCast in
theorem natCast_div_of_dvd {x y : Nat} (h : y ∣ x) (w : (y : α) ≠ 0) :
    ((x / y : Nat) : α) = ((x : α) / (y : α)) := by
  obtain ⟨z, rfl⟩ := h
  by_cases hy : y = 0
  · simp_all [Semiring.natCast_zero]
  · rw [Nat.mul_div_cancel_left _ (by omega)]
    rw [Semiring.natCast_mul, CommSemiring.mul_comm, div_eq_mul_inv, Semiring.mul_assoc,
      mul_inv_cancel w, Semiring.mul_one]

-- This is expensive as an instance. Let's see what breaks without it.
def noNatZeroDivisors.ofIsCharPZero [IsCharP α 0] : NoNatZeroDivisors α := NoNatZeroDivisors.mk' <| by
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
