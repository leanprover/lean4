/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Zero
import Init.Data.Int.DivMod.Lemmas
import Init.Data.Int.Pow
import Init.TacticsExtra

/-!
# A monolithic commutative ring typeclass for internal use in `grind`.

The `Lean.Grind.CommRing` class will be used to convert expressions into the internal representation via polynomials,
with coefficients expressed via `OfNat` and `Neg`.

The `IsCharP α p` typeclass expresses that the ring has characteristic `p`,
i.e. that a coefficient `OfNat.ofNat x : α` is zero if and only if `x % p = 0` (in `Nat`).
See
```
theorem ofNat_ext_iff {x y : Nat} : OfNat.ofNat (α := α) x = OfNat.ofNat (α := α) y ↔ x % p = y % p
theorem ofNat_emod (x : Nat) : OfNat.ofNat (α := α) (x % p) = OfNat.ofNat x
theorem ofNat_eq_iff_of_lt {x y : Nat} (h₁ : x < p) (h₂ : y < p) :
    OfNat.ofNat (α := α) x = OfNat.ofNat (α := α) y ↔ x = y
```
-/

namespace Lean.Grind

class CommRing (α : Type u) extends Add α, Mul α, Neg α, Sub α, HPow α Nat α where
  [ofNat : ∀ n, OfNat α n]
  [intCast : IntCast α]
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  add_comm : ∀ a b : α, a + b = b + a
  add_zero : ∀ a : α, a + 0 = a
  neg_add_cancel : ∀ a : α, -a + a = 0
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  mul_comm : ∀ a b : α, a * b = b * a
  mul_one : ∀ a : α, a * 1 = a
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  zero_mul : ∀ a : α, 0 * a = 0
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  pow_zero : ∀ a : α, a ^ 0 = 1
  pow_succ : ∀ a : α, ∀ n : Nat, a ^ (n + 1) = (a ^ n) * a
  ofNat_succ : ∀ a : Nat, OfNat.ofNat (α := α) (a + 1) = OfNat.ofNat a + 1 := by intros; rfl
  intCast_ofNat : ∀ n : Nat, Int.cast (OfNat.ofNat (α := Int) n) = OfNat.ofNat (α := α) n := by intros; rfl
  intCast_neg : ∀ i : Int, Int.cast (R := α) (-i) = -Int.cast i := by intros; rfl

-- We reduce the priority of these parent instances,
-- so that in downstream libraries with their own `CommRing` class,
-- the path `CommRing -> Add` is found before `CommRing -> Lean.Grind.CommRing -> Add`.
-- (And similarly for the other parents.)
attribute [instance 100] CommRing.toAdd CommRing.toMul CommRing.toNeg CommRing.toSub CommRing.toHPow

-- This is a low-priority instance, to avoid conflicts with existing `OfNat` instances.
attribute [instance 100] CommRing.ofNat

-- This is a low-priority instance, to avoid conflicts with existing `IntCast` instances.
attribute [instance 100] CommRing.intCast

namespace CommRing

variable {α : Type u} [CommRing α]

instance natCastInst : NatCast α where
  natCast n := OfNat.ofNat n

theorem natCast_zero : ((0 : Nat) : α) = 0 := rfl
theorem ofNat_eq_natCast (n : Nat) : OfNat.ofNat n = (n : α) := rfl

theorem ofNat_add (a b : Nat) : OfNat.ofNat (α := α) (a + b) = OfNat.ofNat a + OfNat.ofNat b := by
  induction b with
  | zero => simp [Nat.add_zero, add_zero]
  | succ b ih => rw [Nat.add_succ, ofNat_succ, ih, ofNat_succ b, add_assoc]

theorem natCast_succ (n : Nat) : ((n + 1 : Nat) : α) = ((n : α) + 1) := ofNat_add _ _
theorem natCast_add (a b : Nat) : ((a + b : Nat) : α) = ((a : α) + (b : α)) := ofNat_add _ _

theorem zero_add (a : α) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem add_neg_cancel (a : α) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

theorem add_left_comm (a b c : α) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, ← add_assoc, add_comm a]

theorem one_mul (a : α) : 1 * a = a := by
  rw [mul_comm, mul_one]

theorem right_distrib (a b c : α) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c, mul_comm c]

theorem mul_zero (a : α) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem mul_left_comm (a b c : α) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, ← mul_assoc, mul_comm a]

theorem ofNat_mul (a b : Nat) : OfNat.ofNat (α := α) (a * b) = OfNat.ofNat a * OfNat.ofNat b := by
  induction b with
  | zero => simp [Nat.mul_zero, mul_zero]
  | succ a ih => rw [Nat.mul_succ, ofNat_add, ih, ofNat_add, left_distrib, mul_one]

theorem natCast_mul (a b : Nat) : ((a * b : Nat) : α) = ((a : α) * (b : α)) := by
  rw [← ofNat_eq_natCast, ofNat_mul, ofNat_eq_natCast, ofNat_eq_natCast]

theorem add_left_inj {a b : α} (c : α) : a + c = b + c ↔ a = b :=
  ⟨fun h => by simpa [add_assoc, add_neg_cancel, add_zero] using (congrArg (· + -c) h),
   fun g => congrArg (· + c) g⟩

theorem add_right_inj (a b c : α) : a + b = a + c ↔ b = c := by
  rw [add_comm a b, add_comm a c, add_left_inj]

theorem neg_zero : (-0 : α) = 0 := by
  rw [← add_left_inj 0, neg_add_cancel, add_zero]

theorem neg_neg (a : α) : -(-a) = a := by
  rw [← add_left_inj (-a), neg_add_cancel, add_neg_cancel]

theorem neg_eq_zero (a : α) : -a = 0 ↔ a = 0 :=
  ⟨fun h => by
    replace h := congrArg (-·) h
    simpa [neg_neg, neg_zero] using h,
   fun h => by rw [h, neg_zero]⟩

theorem neg_add (a b : α) : -(a + b) = -a + -b := by
  rw [← add_left_inj (a + b), neg_add_cancel, add_assoc (-a), add_comm a b, ← add_assoc (-b),
    neg_add_cancel, zero_add, neg_add_cancel]

theorem neg_sub (a b : α) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, neg_add, neg_neg, sub_eq_add_neg, add_comm]

theorem sub_self (a : α) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

theorem sub_eq_iff {a b c : α} : a - b = c ↔ a = c + b := by
  rw [sub_eq_add_neg]
  constructor
  next => intro; subst c; rw [add_assoc, neg_add_cancel, add_zero]
  next => intro; subst a; rw [add_assoc, add_comm b, neg_add_cancel, add_zero]

theorem sub_eq_zero_iff {a b : α} : a - b = 0 ↔ a = b := by
  simp [sub_eq_iff, zero_add]

theorem intCast_zero : ((0 : Int) : α) = 0 := intCast_ofNat 0
theorem intCast_one : ((1 : Int) : α) = 1 := intCast_ofNat 1
theorem intCast_neg_one : ((-1 : Int) : α) = -1 := by rw [intCast_neg, intCast_ofNat]
theorem intCast_natCast (n : Nat) : ((n : Int) : α) = (n : α) := intCast_ofNat n
theorem intCast_natCast_add_one (n : Nat) : ((n + 1 : Int) : α) = (n : α) + 1 := by
  rw [← Int.natCast_add_one, intCast_natCast, natCast_add, ofNat_eq_natCast]
theorem intCast_negSucc (n : Nat) : ((-(n + 1) : Int) : α) = -((n : α) + 1) := by
  rw [intCast_neg, ← Int.natCast_add_one, intCast_natCast, ofNat_eq_natCast, natCast_add]
theorem intCast_nat_add {x y : Nat} : ((x + y : Int) : α) = ((x : α) + (y : α)) := by
  rw [Int.ofNat_add_ofNat, intCast_natCast, natCast_add]
theorem intCast_nat_sub {x y : Nat} (h : x ≥ y) : (((x - y : Nat) : Int) : α) = ((x : α) - (y : α)) := by
  induction x with
  | zero =>
    have : y = 0 := by omega
    simp [this, intCast_zero, natCast_zero, sub_eq_add_neg, zero_add, neg_zero]
  | succ x ih =>
    by_cases h : x + 1 = y
    · simp [h, intCast_zero, sub_self]
    · have : ((x + 1 - y : Nat) : Int) = (x - y : Nat) + 1 := by omega
      rw [this, intCast_natCast_add_one]
      specialize ih (by omega)
      rw [intCast_natCast] at ih
      rw [ih, natCast_succ, sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_comm _ 1, ← add_assoc]
theorem intCast_add (x y : Int) : ((x + y : Int) : α) = ((x : α) + (y : α)) :=
  match x, y with
  | (x : Nat), (y : Nat) => by
    rw [intCast_nat_add, intCast_natCast, intCast_natCast]
  | (x : Nat), (-(y + 1 : Nat)) => by
    by_cases h : x ≥ y + 1
    · have : (x + -(y+1 : Nat) : Int) = ((x - (y + 1) : Nat) : Int) := by omega
      rw [this, intCast_neg, intCast_nat_sub h, intCast_natCast, intCast_natCast, sub_eq_add_neg]
    · have : (x + -(y+1 : Nat) : Int) = (-(y + 1 - x : Nat) : Int) := by omega
      rw [this, intCast_neg, intCast_nat_sub (by omega), intCast_natCast, intCast_neg, intCast_natCast,
        neg_sub, sub_eq_add_neg]
  | (-(x + 1 : Nat)), (y : Nat) => by
    by_cases h : y ≥ x+ 1
    · have : (-(x+1 : Nat) + y : Int) = ((y - (x + 1) : Nat) : Int) := by omega
      rw [this, intCast_neg, intCast_nat_sub h, intCast_natCast, intCast_natCast, sub_eq_add_neg, add_comm]
    · have : (-(x+1 : Nat) + y : Int) = (-(x + 1 - y : Nat) : Int) := by omega
      rw [this, intCast_neg, intCast_nat_sub (by omega), intCast_natCast, intCast_neg, intCast_natCast,
        neg_sub, sub_eq_add_neg, add_comm]
  | (-(x + 1 : Nat)), (-(y + 1 : Nat)) => by
    rw [← Int.neg_add, intCast_neg, intCast_nat_add, neg_add, intCast_neg, intCast_neg, intCast_natCast, intCast_natCast]
theorem intCast_sub (x y : Int) : ((x - y : Int) : α) = ((x : α) - (y : α)) := by
  rw [Int.sub_eq_add_neg, intCast_add, intCast_neg, sub_eq_add_neg]

theorem neg_eq_neg_one_mul (a : α) : -a = (-1) * a := by
  rw [← add_left_inj a, neg_add_cancel]
  conv => rhs; arg 2; rw [← one_mul a]
  rw [← right_distrib, ← intCast_neg_one, ← intCast_one (α := α)]
  simp [← intCast_add, intCast_zero, zero_mul]

theorem neg_mul (a b : α) : (-a) * b = -(a * b) := by
  rw [neg_eq_neg_one_mul a, neg_eq_neg_one_mul (a * b), mul_assoc]

theorem mul_neg (a b : α) : a * (-b) = -(a * b) := by
  rw [mul_comm, neg_mul, mul_comm]

theorem intCast_nat_mul (x y : Nat) : ((x * y : Int) : α) = ((x : α) * (y : α)) := by
  rw [Int.ofNat_mul_ofNat, intCast_natCast, natCast_mul]

theorem intCast_mul (x y : Int) : ((x * y : Int) : α) = ((x : α) * (y : α)) :=
  match x, y with
  | (x : Nat), (y : Nat) => by
    rw [intCast_nat_mul, intCast_natCast, intCast_natCast]
  | (x : Nat), (-(y + 1 : Nat)) => by
    rw [Int.mul_neg, intCast_neg, intCast_nat_mul, intCast_neg, mul_neg, intCast_natCast, intCast_natCast]
  | (-(x + 1 : Nat)), (y : Nat) => by
    rw [Int.neg_mul, intCast_neg, intCast_nat_mul, intCast_neg, neg_mul, intCast_natCast, intCast_natCast]
  | (-(x + 1 : Nat)), (-(y + 1 : Nat)) => by
    rw [Int.neg_mul_neg, intCast_neg, intCast_neg, neg_mul, mul_neg, neg_neg, intCast_nat_mul,
      intCast_natCast, intCast_natCast]

theorem intCast_pow (x : Int) (k : Nat) : ((x ^ k : Int) : α) = (x : α) ^ k := by
  induction k
  next => simp [pow_zero, Int.pow_zero, intCast_one]
  next k ih => simp [pow_succ, Int.pow_succ, intCast_mul, *]

theorem pow_add (a : α) (k₁ k₂ : Nat) : a ^ (k₁ + k₂) = a^k₁ * a^k₂ := by
  induction k₂
  next => simp [pow_zero, mul_one]
  next k₂ ih => rw [Nat.add_succ, pow_succ, pow_succ, ih, mul_assoc]

end CommRing

open CommRing

class IsCharP (α : Type u) [CommRing α] (p : outParam Nat) where
  ofNat_eq_zero_iff (p) : ∀ (x : Nat), OfNat.ofNat (α := α) x = 0 ↔ x % p = 0

namespace IsCharP

variable (p)  {α : Type u} [CommRing α] [IsCharP α p]

theorem natCast_eq_zero_iff (x : Nat) : (x : α) = 0 ↔ x % p = 0 :=
  ofNat_eq_zero_iff p x

theorem intCast_eq_zero_iff (x : Int) : (x : α) = 0 ↔ x % p = 0 :=
  match x with
  | (x : Nat) => by
    have := ofNat_eq_zero_iff (α := α) p (x := x)
    rw [Int.ofNat_mod_ofNat, intCast_natCast]
    norm_cast
  | -(x + 1 : Nat) => by
    rw [Int.neg_emod, Int.ofNat_mod_ofNat, intCast_neg, intCast_natCast, neg_eq_zero]
    have := ofNat_eq_zero_iff (α := α) p (x := x + 1)
    rw [ofNat_eq_natCast] at this
    rw [this]
    simp only [Int.ofNat_dvd]
    simp only [← Nat.dvd_iff_mod_eq_zero, Int.natAbs_natCast, Int.natCast_add,
      Int.cast_ofNat_Int, ite_eq_left_iff]
    by_cases h : p ∣ x + 1
    · simp [h]
    · simp only [h, not_false_eq_true, Int.natCast_add, Int.cast_ofNat_Int,
        forall_const, false_iff, ne_eq]
      by_cases w : p = 0
      · simp [w]
        omega
      · have : ((x + 1) % p) < p := Nat.mod_lt _ (by omega)
        omega

theorem intCast_ext_iff {x y : Int} : (x : α) = (y : α) ↔ x % p = y % p := by
  constructor
  · intro h
    replace h : ((x - y : Int) : α) = 0 := by rw [intCast_sub, h, sub_self]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr ((intCast_eq_zero_iff p _).mp h)
  · intro h
    have : ((x - y : Int) : α) = 0 :=
      (intCast_eq_zero_iff p _).mpr (by rw [Int.sub_emod, h, Int.sub_self, Int.zero_emod])
    replace this := congrArg (· + (y : α)) this
    simpa [intCast_sub, zero_add, sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero] using this

theorem ofNat_ext_iff {x y : Nat} : OfNat.ofNat (α := α) x = OfNat.ofNat (α := α) y ↔ x % p = y % p := by
  have := intCast_ext_iff (α := α) p (x := x) (y := y)
  simp only [intCast_natCast, ← Int.natCast_emod] at this
  simp only [ofNat_eq_natCast]
  norm_cast at this

theorem ofNat_ext {x y : Nat} (h : x % p = y % p) : OfNat.ofNat (α := α) x = OfNat.ofNat (α := α) y := (ofNat_ext_iff p).mpr h

theorem natCast_ext {x y : Nat} (h : x % p = y % p) : (x : α) = (y : α) := ofNat_ext _ h

theorem natCast_ext_iff {x y : Nat} : (x : α) = (y : α) ↔ x % p = y % p :=
  ofNat_ext_iff p

theorem intCast_emod (x : Int) : ((x % p : Int) : α) = (x : α) := by
  rw [intCast_ext_iff p, Int.emod_emod]

theorem natCast_emod (x : Nat) : ((x % p : Nat) : α) = (x : α) := by
  simp only [← intCast_natCast]
  rw [Int.natCast_emod, intCast_emod]

theorem ofNat_emod (x : Nat) : OfNat.ofNat (α := α) (x % p) = OfNat.ofNat x :=
  natCast_emod _ _

theorem ofNat_eq_zero_iff_of_lt {x : Nat} (h : x < p) : OfNat.ofNat (α := α) x = 0 ↔ x = 0 := by
  rw [ofNat_eq_zero_iff p, Nat.mod_eq_of_lt h]

theorem ofNat_eq_iff_of_lt {x y : Nat} (h₁ : x < p) (h₂ : y < p) :
    OfNat.ofNat (α := α) x = OfNat.ofNat (α := α) y ↔ x = y := by
  rw [ofNat_ext_iff p, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂]

theorem natCast_eq_zero_iff_of_lt {x : Nat} (h : x < p) : (x : α) = 0 ↔ x = 0 := by
  rw [natCast_eq_zero_iff p, Nat.mod_eq_of_lt h]

theorem natCast_eq_iff_of_lt {x y : Nat} (h₁ : x < p) (h₂ : y < p) :
    (x : α) = (y : α) ↔ x = y := by
  rw [natCast_ext_iff p, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂]

end IsCharP

/--
Special case of Mathlib's `NoZeroSMulDivisors Nat α`.
-/
class NoZeroNatDivisors (α : Type u) [CommRing α] where
  no_zero_nat_divisors : ∀ (k : Nat) (a : α), k ≠ 0 → OfNat.ofNat (α := α) k * a = 0 → a = 0

export NoZeroNatDivisors (no_zero_nat_divisors)

theorem no_zero_int_divisors {α : Type u} [CommRing α] [NoZeroNatDivisors α] {k : Int} {a : α}
    : k ≠ 0 → k * a = 0 → a = 0 := by
  match k with
  | (k : Nat) =>
    simp [intCast_natCast]
    intro h₁ h₂
    replace h₁ : k ≠ 0 := by intro h; simp [h] at h₁
    exact no_zero_nat_divisors k a h₁ h₂
  | -(k+1 : Nat) =>
    rw [Int.natCast_add, ← Int.natCast_add, intCast_neg, intCast_natCast]
    intro _ h
    replace h := congrArg (-·) h; simp at h
    rw [← neg_mul, neg_neg, neg_zero] at h
    exact no_zero_nat_divisors (k+1) a (Nat.succ_ne_zero _) h

end Lean.Grind
