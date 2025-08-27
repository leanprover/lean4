/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.Int.Order
public import Init.Grind.ToInt
import all Init.Grind.ToInt

public section

namespace Lean.Grind

/--
A type where addition is right-cancellative, i.e. `a + c = b + c` implies `a = b`.
-/
class AddRightCancel (M : Type u) [Add M] where
  /-- Addition is right-cancellative. -/
  add_right_cancel : ∀ a b c : M, a + c = b + c → a = b

/-- A type with zero and addition,
where addition is commutative and associative,
and the zero is the right identity for addition. -/
class AddCommMonoid (M : Type u) extends Zero M, Add M where
  /-- Zero is the right identity for addition. -/
  add_zero : ∀ a : M, a + 0 = a
  /-- Addition is commutative. -/
  add_comm : ∀ a b : M, a + b = b + a
  /-- Addition is associative. -/
  add_assoc : ∀ a b c : M, a + b + c = a + (b + c)

attribute [instance 100] AddCommMonoid.toZero AddCommMonoid.toAdd

/-- A type with zero, addition, negation, and subtraction,
where addition is commutative and associative,
and negation is the left inverse of addition. -/
class AddCommGroup (M : Type u) extends AddCommMonoid M, Neg M, Sub M where
  /-- Negation is the left inverse of addition. -/
  neg_add_cancel : ∀ a : M, -a + a = 0
  /-- Subtraction is addition of the negative. -/
  sub_eq_add_neg : ∀ a b : M, a - b = a + -b

attribute [instance 100] AddCommGroup.toAddCommMonoid AddCommGroup.toNeg AddCommGroup.toSub

/--
A module over the natural numbers, i.e. a type with zero, addition, and scalar multiplication by natural numbers,
satisfying appropriate compatibilities.

Equivalently, an additive commutative monoid.

Use `IntModule` if the type has negation.
-/
class NatModule (M : Type u) extends AddCommMonoid M where
  /-- Scalar multiplication by natural numbers. -/
  [nsmul : SMul Nat M]
  /-- Scalar multiplication by zero is zero. -/
  zero_nsmul : ∀ a : M, 0 • a = 0
  /-- Scalar multiplication by a successor. -/
  add_one_nsmul : ∀ n : Nat, ∀ a : M, (n + 1) • a = n • a + a

attribute [instance 100] NatModule.toAddCommMonoid NatModule.nsmul

/--
A module over the integers, i.e. a type with zero, addition, negation, subtraction, and scalar multiplication by integers,
satisfying appropriate compatibilities.

Equivalently, an additive commutative group.
-/
class IntModule (M : Type u) extends AddCommGroup M where
  /-- Scalar multiplication by natural numbers. -/
  [nsmul : SMul Nat M]
  /-- Scalar multiplication by integers. -/
  [zsmul : SMul Int M]
  /-- Scalar multiplication by zero is zero. -/
  zero_zsmul : ∀ a : M, (0 : Int) • a = 0
  /-- Scalar multiplication by one is the identity. -/
  one_zsmul : ∀ a : M, (1 : Int) • a = a
  /-- Scalar multiplication is distributive over addition in the integers. -/
  add_zsmul : ∀ n m : Int, ∀ a : M, (n + m) • a = n • a + m • a
  /-- Scalar multiplication by natural numbers is consistent with scalar multiplication by integers. -/
  zsmul_natCast_eq_nsmul : ∀ n : Nat, ∀ a : M, (n : Int) • a = n • a

attribute [instance 100] IntModule.toAddCommGroup IntModule.zsmul

namespace IntModule

variable {M : Type u} [IntModule M]

instance (priority := 100) toNatModule [I : IntModule M] : NatModule M :=
  { I with
    zero_nsmul a := by rw [← zsmul_natCast_eq_nsmul, Int.natCast_zero, zero_zsmul]
    add_one_nsmul n a := by rw [← zsmul_natCast_eq_nsmul, Int.natCast_add_one, add_zsmul,
      zsmul_natCast_eq_nsmul, one_zsmul] }

end IntModule

namespace AddCommMonoid

variable {M : Type u} [AddCommMonoid M]

theorem zero_add (a : M) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem add_left_comm (a b c : M) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, ← add_assoc, add_comm a]

end AddCommMonoid

namespace AddCommGroup

variable {M : Type u} [AddCommGroup M]
open AddCommMonoid

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

theorem add_sub_cancel {a b : M} : a + b - b = a := by
  rw [sub_eq_add_neg, add_assoc, add_neg_cancel, add_zero]

theorem sub_add_cancel {a b : M} : a - b + b = a := by
  rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]

theorem neg_eq_iff (a b : M) : -a = b ↔ a = -b := by
  constructor
  · intro h
    rw [← neg_neg a, h]
  · intro h
    rw [← neg_neg b, h]

end AddCommGroup

namespace NatModule

variable {M : Type u} [NatModule M]

theorem one_nsmul (a : M) : 1 • a = a := by
  rw [← Nat.zero_add 1, add_one_nsmul, zero_nsmul, AddCommMonoid.zero_add]

theorem add_nsmul (n m : Nat) (a : M) : (n + m) • a = n • a + m • a := by
  induction m with
  | zero => rw [Nat.add_zero, zero_nsmul, AddCommMonoid.add_zero]
  | succ m ih => rw [add_one_nsmul, ← Nat.add_assoc, add_one_nsmul, ih, AddCommMonoid.add_assoc]

theorem nsmul_zero (n : Nat) : n • (0 : M) = 0 := by
  induction n with
  | zero => rw [zero_nsmul]
  | succ n ih => rw [add_one_nsmul, ih, AddCommMonoid.zero_add]

theorem nsmul_add (n : Nat) (a b : M) : n • (a + b) = n • a + n • b := by
  induction n with
  | zero => rw [zero_nsmul, zero_nsmul, zero_nsmul, AddCommMonoid.zero_add]
  | succ n ih => rw [add_one_nsmul, add_one_nsmul, add_one_nsmul, ih, AddCommMonoid.add_assoc,
      AddCommMonoid.add_left_comm (n • b), AddCommMonoid.add_assoc]

theorem mul_nsmul (n m : Nat) (a : M) : (n * m) • a = n • (m • a) := by
  induction n with
  | zero => simp [zero_nsmul]
  | succ n ih =>
    rw [Nat.add_one_mul, add_nsmul, ih, add_nsmul, one_nsmul]

end NatModule

namespace IntModule

open NatModule AddCommGroup

variable {M : Type u} [IntModule M]

theorem neg_zsmul (n : Int) (a : M) : (-n) • a = - (n • a) := by
  apply (add_left_inj (n • a)).mp
  rw [← add_zsmul, Int.add_left_neg, zero_zsmul, neg_add_cancel]

theorem zsmul_zero (n : Int) : n • (0 : M) = 0 := by
  match n with
  | (n : Nat) => rw [zsmul_natCast_eq_nsmul, NatModule.nsmul_zero]
  | -(n + 1 : Nat) => rw [neg_zsmul, zsmul_natCast_eq_nsmul, NatModule.nsmul_zero, neg_zero]

theorem zsmul_add (n : Int) (a b : M) : n • (a + b) = n • a + n • b := by
  match n with
  | (n : Nat) => rw [zsmul_natCast_eq_nsmul, NatModule.nsmul_add, zsmul_natCast_eq_nsmul, zsmul_natCast_eq_nsmul]
  | -(n + 1 : Nat) => rw [neg_zsmul, zsmul_natCast_eq_nsmul, NatModule.nsmul_add,
      neg_zsmul, zsmul_natCast_eq_nsmul, neg_zsmul, zsmul_natCast_eq_nsmul, neg_add]

theorem zsmul_neg (n : Int) (a : M) : n • (-a) = - (n • a) := by
  apply (add_left_inj (n • a)).mp
  rw [← zsmul_add, neg_add_cancel, neg_add_cancel, zsmul_zero]

theorem zsmul_sub (k : Int) (a b : M) : k • (a - b) = k • a - k • b := by
  rw [sub_eq_add_neg, zsmul_add, zsmul_neg, ← sub_eq_add_neg]

theorem sub_zsmul (k₁ k₂ : Int) (a : M) : (k₁ - k₂) • a = k₁ • a - k₂ • a := by
  rw [Int.sub_eq_add_neg, add_zsmul, neg_zsmul, ← sub_eq_add_neg]

private theorem mul_zsmul_aux (n : Nat) (m : Int) (a : M) :
    ((n : Int) * m) • a = (n : Int) • (m • a) := by
  induction n with
  | zero => simp [zero_zsmul]
  | succ n ih =>
    rw [Int.natCast_add, Int.add_mul, add_zsmul, Int.natCast_one,
      Int.one_mul, add_zsmul, one_zsmul, ih]

theorem mul_zsmul (n m : Int) (a : M) : (n * m) • a = n • (m • a) := by
  match n with
  | (n : Nat) => exact mul_zsmul_aux n m a
  | -(n + 1 : Nat) => rw [Int.neg_mul, neg_zsmul, mul_zsmul_aux, neg_zsmul]

end IntModule

/--
We say a module has no natural number zero divisors if
`k ≠ 0` and `k * a = k * b` implies `a = b` (here `k` is a natural number and `a` and `b` are element of the module).

For a module over the integers this is equivalent to
`k ≠ 0` and `k * a = 0` implies `a = 0`.
(See the alternative constructor `NoNatZeroDivisors.mk'`,
and the theorem `eq_zero_of_mul_eq_zero`.)
-/
class NoNatZeroDivisors (α : Type u) [NatModule α] where
  /-- If `k * a ≠ k * b` then `k ≠ 0` or `a ≠ b`.-/
  no_nat_zero_divisors : ∀ (k : Nat) (a b : α), k ≠ 0 → k • a = k • b → a = b

export NoNatZeroDivisors (no_nat_zero_divisors)

namespace NoNatZeroDivisors

/-- Alternative constructor for `NoNatZeroDivisors` when we have an `IntModule`. -/
def mk' {α} [IntModule α]
    (eq_zero_of_mul_eq_zero : ∀ (k : Nat) (a : α), k ≠ 0 → k • a = 0 → a = 0) :
    NoNatZeroDivisors α where
  no_nat_zero_divisors k a b h₁ h₂ := by
    rw [← AddCommGroup.sub_eq_zero_iff, ← IntModule.zsmul_natCast_eq_nsmul,
      ← IntModule.zsmul_natCast_eq_nsmul, ← IntModule.zsmul_sub,
      IntModule.zsmul_natCast_eq_nsmul] at h₂
    rw [← AddCommGroup.sub_eq_zero_iff]
    apply eq_zero_of_mul_eq_zero k (a - b) h₁ h₂

theorem eq_zero_of_mul_eq_zero {α : Type u} [NatModule α] [NoNatZeroDivisors α] {k : Nat} {a : α}
    : k ≠ 0 → k • a = 0 → a = 0 := by
  intro h₁ h₂
  replace h₁ : k ≠ 0 := by intro h; simp [h] at h₁
  exact no_nat_zero_divisors k a 0 h₁ (by rwa [NatModule.nsmul_zero])

end NoNatZeroDivisors

instance [ToInt α (IntInterval.co lo hi)] [AddCommGroup α] [ToInt.Zero α (IntInterval.co lo hi)] [ToInt.Add α (IntInterval.co lo hi)] : ToInt.Neg α (IntInterval.co lo hi) where
  toInt_neg x := by
    have := (ToInt.Add.toInt_add (-x) x).symm
    rw [AddCommGroup.neg_add_cancel, ToInt.Zero.toInt_zero, ← ToInt.Zero.wrap_zero (α := α)] at this
    rw [IntInterval.wrap_eq_wrap_iff] at this
    simp at this
    rw [← ToInt.wrap_toInt]
    rw [IntInterval.wrap_eq_wrap_iff]
    simpa

instance [ToInt α (IntInterval.co lo hi)] [AddCommGroup α] [ToInt.Add α (IntInterval.co lo hi)] [ToInt.Neg α (IntInterval.co lo hi)] : ToInt.Sub α (IntInterval.co lo hi) :=
  ToInt.Sub.of_sub_eq_add_neg AddCommGroup.sub_eq_add_neg (by simp)

end Lean.Grind
