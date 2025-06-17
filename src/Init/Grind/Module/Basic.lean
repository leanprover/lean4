/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Int.Order
import Init.Grind.ToInt

namespace Lean.Grind

class AddRightCancel (M : Type u) [Add M] where
  add_right_cancel : ∀ a b c : M, a + c = b + c → a = b

class NatModule (M : Type u) extends Zero M, Add M, HMul Nat M M where
  add_zero : ∀ a : M, a + 0 = a
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

namespace NatModule

variable {M : Type u} [NatModule M]

theorem zero_add (a : M) : 0 + a = a := by
  rw [add_comm, add_zero]

end NatModule

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

instance (priority := 100) (M : Type u) [IntModule M] : SMul Nat M where
  smul a x := (a : Int) * x

instance (priority := 100) (M : Type u) [IntModule M] : SMul Int M where
  smul a x := a * x

theorem zero_add (a : M) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem add_neg_cancel (a : M) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

theorem add_left_comm (a b c : M) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, ← add_assoc, add_comm a]

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

theorem add_sub_cancel {a b : M} : a + b - b = a := by
  rw [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero]

theorem sub_add_cancel {a b : M} : a - b + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

theorem neg_hmul (n : Int) (a : M) : (-n) * a = - (n * a) := by
  apply (add_left_inj (n * a)).mp
  rw [← add_hmul, Int.add_left_neg, zero_hmul, neg_add_cancel]

theorem hmul_neg (n : Int) (a : M) : n * (-a) = - (n * a) := by
  apply (add_left_inj (n * a)).mp
  rw [← hmul_add, neg_add_cancel, neg_add_cancel, hmul_zero]

theorem hmul_sub (k : Int) (a b : M) : k * (a - b) = k * a - k * b := by
  rw [sub_eq_add_neg, hmul_add, hmul_neg, ← sub_eq_add_neg]

theorem sub_hmul (k₁ k₂ : Int) (a : M) : (k₁ - k₂) * a = k₁ * a - k₂ * a := by
  rw [Int.sub_eq_add_neg, add_hmul, neg_hmul, ← sub_eq_add_neg]

end IntModule

/--
Special case of Mathlib's `NoZeroSMulDivisors Nat α`.
-/
class NoNatZeroDivisors (α : Type u) [Zero α] [HMul Nat α α] where
  no_nat_zero_divisors : ∀ (k : Nat) (a : α), k ≠ 0 → k * a = 0 → a = 0

export NoNatZeroDivisors (no_nat_zero_divisors)

instance [ToInt α (some lo) (some hi)] [IntModule α] [ToInt.Zero α (some lo) (some hi)] [ToInt.Add α (some lo) (some hi)] : ToInt.Neg α (some lo) (some hi) where
  toInt_neg x := by
    have := (ToInt.Add.toInt_add (-x) x).symm
    rw [IntModule.neg_add_cancel, ToInt.Zero.toInt_zero] at this
    rw [ToInt.wrap_eq_wrap_iff] at this
    simp at this
    rw [← ToInt.wrap_toInt]
    rw [ToInt.wrap_eq_wrap_iff]
    simpa

instance [ToInt α (some lo) (some hi)] [IntModule α] [ToInt.Add α (some lo) (some hi)] [ToInt.Neg α (some lo) (some hi)] : ToInt.Sub α (some lo) (some hi) :=
  ToInt.Sub.of_sub_eq_add_neg IntModule.sub_eq_add_neg

end Lean.Grind
