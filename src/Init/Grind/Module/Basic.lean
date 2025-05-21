/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Int.Order

namespace Lean.Grind

class NatModule (M : Type u) extends Zero M, Add M, HMul Nat M M where
  add_zero : ∀ a : M, a + 0 = a
  zero_add : ∀ a : M, 0 + a = a
  add_comm : ∀ a b : M, a + b = b + a
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  zero_hmul : ∀ a : M, 0 * a = 0
  one_hmul : ∀ a : M, 1 * a = a
  add_hmul : ∀ n m : Nat, ∀ a : M, (n + m) * a = n * a + m * a
  hmul_zero : ∀ n : Nat, n * (0 : M) = 0
  hmul_add : ∀ n : Nat, ∀ a b : M, n * (a + b) = n * a + n * b
  mul_hmul : ∀ n m : Nat, ∀ a : M, (n * m) * a = n * (m * a)

attribute [instance 100] NatModule.toZero NatModule.toAdd NatModule.toHMul

class IntModule (M : Type u) extends Zero M, Add M, Neg M, Sub M, HMul Int M M where
  add_zero : ∀ a : M, a + 0 = a
  zero_add : ∀ a : M, 0 + a = a
  add_comm : ∀ a b : M, a + b = b + a
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)
  zero_hmul : ∀ a : M, (0 : Int) * a = 0
  one_hmul : ∀ a : M, (1 : Int) * a = a
  add_hmul : ∀ n m : Int, ∀ a : M, (n + m) * a = n * a + m * a
  hmul_zero : ∀ n : Int, n * (0 : M) = 0
  hmul_add : ∀ n : Int, ∀ a b : M, n * (a + b) = n * a + n * b
  mul_hmul : ∀ n m : Int, ∀ a : M, (n * m) * a = n * (m * a)
  neg_add_cancel : ∀ a : M, -a + a = 0
  sub_eq_add_neg : ∀ a b : M, a - b = a + -b

namespace IntModule

attribute [instance 100] IntModule.toZero IntModule.toAdd IntModule.toNeg IntModule.toSub IntModule.toHMul

instance toNatModule (M : Type u) [i : IntModule M] : NatModule M :=
  { i with
    hMul a x := (a : Int) * x
    hmul_zero := by simp [IntModule.hmul_zero]
    add_hmul := by simp [IntModule.add_hmul]
    hmul_add := by simp [IntModule.hmul_add]
    mul_hmul := by simp [IntModule.mul_hmul] }

variable {M : Type u} [IntModule M]

theorem add_neg_cancel (a : M) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

theorem add_left_inj {a b : M} (c : M) : a + c = b + c ↔ a = b :=
  ⟨fun h => by simpa [add_assoc, add_neg_cancel, add_zero] using (congrArg (· + -c) h),
   fun g => congrArg (· + c) g⟩

theorem add_right_inj (a b c : M) : a + b = a + c ↔ b = c := by
  rw [add_comm a b, add_comm a c, add_left_inj]

theorem neg_zero : (-0 : M) = 0 := by
  rw [← add_left_inj 0, neg_add_cancel, add_zero]

theorem neg_neg (a : M) : -(-a) = a := by
  rw [← add_left_inj (-a), neg_add_cancel, add_neg_cancel]

theorem neg_eq_zero (a : M) : -a = 0 ↔ a = 0 :=
  ⟨fun h => by
    replace h := congrArg (-·) h
    simpa [neg_neg, neg_zero] using h,
   fun h => by rw [h, neg_zero]⟩

theorem neg_add (a b : M) : -(a + b) = -a + -b := by
  rw [← add_left_inj (a + b), neg_add_cancel, add_assoc (-a), add_comm a b, ← add_assoc (-b),
    neg_add_cancel, zero_add, neg_add_cancel]

theorem neg_sub (a b : M) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, neg_add, neg_neg, sub_eq_add_neg, add_comm]

theorem sub_self (a : M) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem sub_eq_iff {a b c : M} : a - b = c ↔ a = c + b := by
  rw [sub_eq_add_neg]
  constructor
  next => intro; subst c; rw [add_assoc, neg_add_cancel, add_zero]
  next => intro; subst a; rw [add_assoc, add_comm b, neg_add_cancel, add_zero]

theorem sub_eq_zero_iff {a b : M} : a - b = 0 ↔ a = b := by
  simp [sub_eq_iff, zero_add]

theorem neg_hmul (n : Int) (a : M) : (-n) * a = - (n * a) := by
  apply (add_left_inj (n * a)).mp
  rw [← add_hmul, Int.add_left_neg, zero_hmul, neg_add_cancel]

theorem hmul_neg (n : Int) (a : M) : n * (-a) = - (n * a) := by
  apply (add_left_inj (n * a)).mp
  rw [← hmul_add, neg_add_cancel, neg_add_cancel, hmul_zero]

end IntModule

/-- A preorder is a reflexive, transitive relation `≤` with `a < b` defined in the obvious way. -/
class Preorder (α : Type u) extends LE α, LT α where
  le_refl : ∀ a : α, a ≤ a
  le_trans : ∀ {a b c : α}, a ≤ b → b ≤ c → a ≤ c
  lt := fun a b => a ≤ b ∧ ¬b ≤ a
  lt_iff_le_not_le : ∀ {a b : α}, a < b ↔ a ≤ b ∧ ¬b ≤ a := by intros; rfl

namespace Preorder

variable {α : Type u} [Preorder α]

theorem le_of_lt {a b : α} (h : a < b) : a ≤ b := (lt_iff_le_not_le.mp h).1

theorem lt_of_lt_of_le {a b c : α} (h₁ : a < b) (h₂ : b ≤ c) : a < c := by
  simp [lt_iff_le_not_le] at h₁ ⊢
  exact ⟨le_trans h₁.1 h₂, fun h => h₁.2 (le_trans h₂ h)⟩

theorem lt_of_le_of_lt {a b c : α} (h₁ : a ≤ b) (h₂ : b < c) : a < c := by
  simp [lt_iff_le_not_le] at h₂ ⊢
  exact ⟨le_trans h₁ h₂.1, fun h => h₂.2 (le_trans h h₁)⟩

theorem lt_trans {a b c : α} (h₁ : a < b) (h₂ : b < c) : a < c :=
  lt_of_lt_of_le h₁ (le_of_lt h₂)

theorem lt_irrefl {a : α} (h : a < a) : False := by
  simp [lt_iff_le_not_le] at h

end Preorder

class IntModule.IsOrdered (M : Type u) [Preorder M] [IntModule M] where
  neg_le_iff : ∀ a b : M, -a ≤ b ↔ -b ≤ a
  add_le_left : ∀ {a b : M}, a ≤ b → (c : M) → a + c ≤ b + c
  hmul_pos : ∀ (k : Int) {a : M}, 0 < a → (0 < k ↔ 0 < k * a)
  hmul_nonneg : ∀ {k : Int} {a : M}, 0 ≤ k → 0 ≤ a → 0 ≤ k * a

namespace IntModule.IsOrdered

variable {M : Type u} [Preorder M] [IntModule M] [IntModule.IsOrdered M]

theorem le_neg_iff {a b : M} : a ≤ -b ↔ b ≤ -a := by
  conv => lhs; rw [← neg_neg a]
  rw [neg_le_iff, neg_neg]

theorem neg_lt_iff {a b : M} : -a < b ↔ -b < a := by
  simp [Preorder.lt_iff_le_not_le]
  rw [neg_le_iff, le_neg_iff]

theorem lt_neg_iff {a b : M} : a < -b ↔ b < -a := by
  conv => lhs; rw [← neg_neg a]
  rw [neg_lt_iff, neg_neg]

theorem neg_nonneg_iff {a : M} : 0 ≤ -a ↔ a ≤ 0 := by
  rw [le_neg_iff, neg_zero]

theorem neg_pos_iff {a : M} : 0 < -a ↔ a < 0 := by
  rw [lt_neg_iff, neg_zero]

theorem add_lt_left {a b : M} (h : a < b) (c : M) : a + c < b + c := by
  simp [Preorder.lt_iff_le_not_le] at h ⊢
  constructor
  · exact add_le_left h.1 _
  · intro w
    apply h.2
    replace w := add_le_left w (-c)
    rw [add_assoc, add_assoc, add_neg_cancel, add_zero, add_zero] at w
    exact w

theorem add_le_right (a : M) {b c : M} (h : b ≤ c) : a + b ≤ a + c := by
  rw [add_comm a b, add_comm a c]
  exact add_le_left h a

theorem add_lt_right (a : M) {b c : M} (h : b < c) : a + b < a + c := by
  rw [add_comm a b, add_comm a c]
  exact add_lt_left h a

theorem hmul_neg (k : Int) {a : M} (h : a < 0) : 0 < k ↔ k * a < 0 := by
  simpa [IntModule.hmul_neg, neg_pos_iff] using hmul_pos k (neg_pos_iff.mpr h)

theorem hmul_nonpos {k : Int} {a : M} (hk : 0 ≤ k) (ha : a ≤ 0) : k * a ≤ 0 := by
  simpa [IntModule.hmul_neg, neg_nonneg_iff] using hmul_nonneg hk (neg_nonneg_iff.mpr ha)



end IntModule.IsOrdered

/--
Special case of Mathlib's `NoZeroSMulDivisors Nat α`.
-/
class NoNatZeroDivisors (α : Type u) [Zero α] [HMul Nat α α] where
  no_nat_zero_divisors : ∀ (k : Nat) (a : α), k ≠ 0 → k * a = 0 → a = 0

export NoNatZeroDivisors (no_nat_zero_divisors)

end Lean.Grind
