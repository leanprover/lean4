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
import Init.Grind.Module.Basic

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

/--
A semiring, i.e. a type equipped with addition, multiplication, and a map from the natural numbers,
satisfying appropriate compatibilities.

Use `Ring` instead if the type also has negation,
`CommSemiring` if the multiplication is commutative,
or `CommRing` if the type has negation and multiplication is commutative.
-/
class Semiring (α : Type u) extends Add α, Mul α, HPow α Nat α where
  /--
  In every semiring there is a canonical map from the natural numbers to the semiring,
  providing the values of `0` and `1`. Note that this function need not be injective.
  -/
  [natCast : NatCast α]
  /--
  Natural number numerals in the semiring.
  The field `ofNat_eq_natCast` ensures that these are (propositionally) equal to the values of `natCast`.
  -/
  [ofNat : ∀ n, OfNat α n]
  /-- Addition is associative. -/
  add_assoc : ∀ a b c : α, a + b + c = a + (b + c)
  /-- Addition is commutative. -/
  add_comm : ∀ a b : α, a + b = b + a
  /-- Zero is the right identity for addition. -/
  add_zero : ∀ a : α, a + 0 = a
  /-- Multiplication is associative. -/
  mul_assoc : ∀ a b c : α, a * b * c = a * (b * c)
  /-- One is the right identity for multiplication. -/
  mul_one : ∀ a : α, a * 1 = a
  /-- One is the left identity for multiplication. -/
  one_mul : ∀ a : α, 1 * a = a
  /-- Left distributivity of multiplication over addition. -/
  left_distrib : ∀ a b c : α, a * (b + c) = a * b + a * c
  /-- Right distributivity of multiplication over addition. -/
  right_distrib : ∀ a b c : α, (a + b) * c = a * c + b * c
  /-- Zero is right absorbing for multiplication. -/
  zero_mul : ∀ a : α, 0 * a = 0
  /-- Zero is left absorbing for multiplication. -/
  mul_zero : ∀ a : α, a * 0 = 0
  /-- The zeroth power of any element is one. -/
  pow_zero : ∀ a : α, a ^ 0 = 1
  /-- The successor power law for exponentiation. -/
  pow_succ : ∀ a : α, ∀ n : Nat, a ^ (n + 1) = (a ^ n) * a
  /-- Numerals are consistently defined with respect to addition. -/
  ofNat_succ : ∀ a : Nat, OfNat.ofNat (α := α) (a + 1) = OfNat.ofNat a + 1 := by intros; rfl
  /-- Numerals are consistently defined with respect to the canonical map from natural numbers. -/
  ofNat_eq_natCast : ∀ n : Nat, OfNat.ofNat (α := α) n = Nat.cast n := by intros; rfl

/--
A ring, i.e. a type equipped with addition, negation, multiplication, and a map from the integers,
satisfying appropriate compatibilities.

Use `CommRing` if the multiplication is commutative.
-/
class Ring (α : Type u) extends Semiring α, Neg α, Sub α where
  /-- In every ring there is a canonical map from the integers to the ring. -/
  [intCast : IntCast α]
  /-- Negation is the left inverse of addition. -/
  neg_add_cancel : ∀ a : α, -a + a = 0
  /-- Subtraction is addition of the negative. -/
  sub_eq_add_neg : ∀ a b : α, a - b = a + -b
  /-- The canonical map from the integers is consistent with the canonical map from the natural numbers. -/
  intCast_ofNat : ∀ n : Nat, Int.cast (OfNat.ofNat (α := Int) n) = OfNat.ofNat (α := α) n := by intros; rfl
  /-- The canonical map from the integers is consistent with negation. -/
  intCast_neg : ∀ i : Int, Int.cast (R := α) (-i) = -Int.cast i := by intros; rfl

/--
A commutative semiring, i.e. a semiring with commutative multiplication.

Use `CommRing` if the type has negation.
-/
class CommSemiring (α : Type u) extends Semiring α where
  /-- Multiplication is commutative. -/
  mul_comm : ∀ a b : α, a * b = b * a
  one_mul := by intro a; rw [mul_comm, mul_one]
  mul_zero := by intro a; rw [mul_comm, zero_mul]
  right_distrib := by intro a b c; rw [mul_comm, left_distrib, mul_comm c, mul_comm c]

/--
A commutative ring, i.e. a ring with commutative multiplication.
-/
class CommRing (α : Type u) extends Ring α, CommSemiring α

-- We reduce the priority of these parent instances,
-- so that in downstream libraries with their own `CommRing` class,
-- the path `CommRing -> Add` is found before `CommRing -> Lean.Grind.CommRing -> Add`.
-- (And similarly for the other parents.)
attribute [instance 100] Semiring.toAdd Semiring.toMul Semiring.toHPow Ring.toNeg Ring.toSub

-- This is a low-priority instance, to avoid conflicts with existing `OfNat`, `NatCast`, and `IntCast` instances.
attribute [instance 100] Semiring.ofNat

attribute [local instance] Semiring.natCast Ring.intCast

-- Verify that the diamond from `CommRing` to `Semiring` via either `CommSemiring` or `Ring` is defeq.
example [CommRing α] : (CommSemiring.toSemiring : Semiring α) = (Ring.toSemiring : Semiring α) := rfl

namespace Semiring

variable {α : Type u} [Semiring α]

theorem natCast_zero : ((0 : Nat) : α) = 0 := (ofNat_eq_natCast 0).symm
theorem natCast_one : ((1 : Nat) : α) = 1 := (ofNat_eq_natCast 1).symm

theorem ofNat_add (a b : Nat) : OfNat.ofNat (α := α) (a + b) = OfNat.ofNat a + OfNat.ofNat b := by
  induction b with
  | zero => simp [Nat.add_zero, add_zero]
  | succ b ih => rw [Nat.add_succ, ofNat_succ, ih, ofNat_succ b, add_assoc]

theorem natCast_add (a b : Nat) : ((a + b : Nat) : α) = ((a : α) + (b : α)) := by
  rw [← ofNat_eq_natCast, ← ofNat_eq_natCast, ofNat_add, ofNat_eq_natCast, ofNat_eq_natCast]
theorem natCast_succ (n : Nat) : ((n + 1 : Nat) : α) = ((n : α) + 1) := by
  rw [natCast_add, natCast_one]

theorem zero_add (a : α) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem add_left_comm (a b c : α) : a + (b + c) = b + (a + c) := by
  rw [← add_assoc, ← add_assoc, add_comm a]

theorem ofNat_mul (a b : Nat) : OfNat.ofNat (α := α) (a * b) = OfNat.ofNat a * OfNat.ofNat b := by
  induction b with
  | zero => simp [Nat.mul_zero, mul_zero]
  | succ a ih => rw [Nat.mul_succ, ofNat_add, ih, ofNat_add, left_distrib, mul_one]

theorem natCast_mul (a b : Nat) : ((a * b : Nat) : α) = ((a : α) * (b : α)) := by
  rw [← ofNat_eq_natCast, ofNat_mul, ofNat_eq_natCast, ofNat_eq_natCast]

theorem pow_one (a : α) : a ^ 1 = a := by
  rw [pow_succ, pow_zero, one_mul]

theorem pow_two (a : α) : a ^ 2 = a * a := by
  rw [pow_succ, pow_one]

theorem pow_add (a : α) (k₁ k₂ : Nat) : a ^ (k₁ + k₂) = a^k₁ * a^k₂ := by
  induction k₂
  next => simp [pow_zero, mul_one]
  next k₂ ih => rw [Nat.add_succ, pow_succ, pow_succ, ih, mul_assoc]

instance : NatModule α where
  hMul a x := a * x
  add_zero := by simp [add_zero]
  add_assoc := by simp [add_assoc]
  add_comm := by simp [add_comm]
  zero_hmul := by simp [natCast_zero, zero_mul]
  one_hmul := by simp [natCast_one, one_mul]
  add_hmul := by simp [natCast_add, right_distrib]
  hmul_zero := by simp [mul_zero]
  hmul_add := by simp [left_distrib]

theorem hmul_eq_natCast_mul {α} [Semiring α] {k : Nat} {a : α} : HMul.hMul (α := Nat) k a = (k : α) * a := rfl

theorem hmul_eq_ofNat_mul {α} [Semiring α] {k : Nat} {a : α} : HMul.hMul (α := Nat) k a = OfNat.ofNat k * a := by
  simp [ofNat_eq_natCast, hmul_eq_natCast_mul]

end Semiring

namespace Ring

open Semiring

variable {α : Type u} [Ring α]

theorem add_neg_cancel (a : α) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

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

theorem neg_eq_iff (a b : α) : -a = b ↔ a = -b := by
  constructor
  · intro h
    rw [← neg_neg a, h]
  · intro h
    rw [← neg_neg b, h]

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
theorem intCast_natCast (n : Nat) : ((n : Int) : α) = (n : α) := by
  erw [intCast_ofNat]
  rw [ofNat_eq_natCast]
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

theorem ofNat_sub {x y : Nat} (h : y ≤ x) : OfNat.ofNat (α := α) (x - y) = OfNat.ofNat x - OfNat.ofNat y := by
  rw [ofNat_eq_natCast, ← intCast_natCast, Int.ofNat_sub h]
  rw [intCast_sub]
  rw [intCast_natCast, intCast_natCast, ofNat_eq_natCast, ofNat_eq_natCast]

theorem neg_ofNat_sub {x y : Nat} (h : y ≤ x) : -OfNat.ofNat (α := α) (x - y) = OfNat.ofNat y - OfNat.ofNat x := by
  rw [neg_eq_iff, ofNat_sub h, neg_sub]

theorem neg_eq_neg_one_mul (a : α) : -a = (-1) * a := by
  rw [← add_left_inj a, neg_add_cancel]
  conv => rhs; arg 2; rw [← one_mul a]
  rw [← right_distrib, ← intCast_neg_one, ← intCast_one (α := α)]
  simp [← intCast_add, intCast_zero, zero_mul]

theorem neg_eq_mul_neg_one (a : α) : -a = a * (-1) := by
  rw [← add_left_inj a, neg_add_cancel]
  conv => rhs; arg 2; rw [← mul_one a]
  rw [← left_distrib, ← intCast_neg_one, ← intCast_one (α := α)]
  simp [← intCast_add, intCast_zero, mul_zero]

theorem neg_mul (a b : α) : (-a) * b = -(a * b) := by
  rw [neg_eq_neg_one_mul a, neg_eq_neg_one_mul (a * b), mul_assoc]

theorem mul_neg (a b : α) : a * (-b) = -(a * b) := by
  rw [neg_eq_mul_neg_one b, neg_eq_mul_neg_one (a * b), mul_assoc]

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

instance : IntModule α where
  hmulInt := ⟨fun a x => a * x⟩
  hmulNat := ⟨fun a x => a * x⟩
  hmul_nat n x := by
    change ((n : Int) : α) * x = (n : α) * x
    rw [intCast_natCast]
  add_zero := by simp [add_zero]
  add_assoc := by simp [add_assoc]
  add_comm := by simp [add_comm]
  zero_hmul := by simp [intCast_zero, zero_mul]
  one_hmul := by simp [intCast_one, one_mul]
  add_hmul := by simp [intCast_add, right_distrib]
  hmul_zero := by simp [mul_zero]
  hmul_add := by simp [left_distrib]
  neg_add_cancel := by simp [neg_add_cancel]
  sub_eq_add_neg := by simp [sub_eq_add_neg]

theorem hmul_eq_intCast_mul {α} [Ring α] {k : Int} {a : α} : HMul.hMul (α := Int) k a = (k : α) * a := rfl

-- Verify that the diamond from `Ring` to `NatModule` via either `Semiring` or `IntModule` is defeq.
example [Ring R] : (Semiring.instNatModule : NatModule R) = (IntModule.toNatModule R) := rfl

end Ring

namespace CommSemiring

open Semiring

variable {α : Type u} [CommSemiring α]

theorem mul_left_comm (a b c : α) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, ← mul_assoc, mul_comm a]

end CommSemiring

open Semiring Ring CommSemiring CommRing

/--
A ring `α` has characteristic `p` if `OfNat.ofNat x = 0` iff `x % p = 0`.

Note that for `p = 0`, we have `x % p = x`, so this says that `OfNat.ofNat` is injective from `Nat` to `α`.

In the case of a semiring, we take the stronger condition that
`OfNat.ofNat x = OfNat.ofNat y` iff `x % p = y % p`.
-/
class IsCharP (α : Type u) [Semiring α] (p : outParam Nat) where
  /-- Two numerals in a semiring are equal iff they are congruent module `p` in the natural numbers. -/
  ofNat_ext_iff (p) : ∀ {x y : Nat}, OfNat.ofNat (α := α) x = OfNat.ofNat (α := α) y ↔ x % p = y % p

namespace IsCharP

section

variable (p) [Semiring α] [IsCharP α p]

theorem ofNat_eq_zero_iff  (x : Nat) :
    OfNat.ofNat (α := α) x = 0 ↔ x % p = 0 := by
  rw [ofNat_ext_iff p]
  simp

theorem ofNat_ext {x y : Nat} (h : x % p = y % p) : OfNat.ofNat (α := α) x = OfNat.ofNat (α := α) y := (ofNat_ext_iff p).mpr h

theorem ofNat_eq_zero_iff_of_lt {x : Nat} (h : x < p) : OfNat.ofNat (α := α) x = 0 ↔ x = 0 := by
  rw [ofNat_eq_zero_iff p, Nat.mod_eq_of_lt h]

theorem ofNat_eq_iff_of_lt {x y : Nat} (h₁ : x < p) (h₂ : y < p) :
    OfNat.ofNat (α := α) x = OfNat.ofNat (α := α) y ↔ x = y := by
  rw [ofNat_ext_iff p, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂]

end

section Semiring

variable (p)

variable [Semiring α] [IsCharP α p]

theorem natCast_eq_zero_iff (x : Nat) : (x : α) = 0 ↔ x % p = 0 := by
  rw [← ofNat_eq_natCast]
  exact ofNat_eq_zero_iff p x

theorem natCast_ext {x y : Nat} (h : x % p = y % p) : (x : α) = (y : α) := by
  rw [← ofNat_eq_natCast, ← ofNat_eq_natCast]
  exact ofNat_ext p h

theorem natCast_ext_iff {x y : Nat} : (x : α) = (y : α) ↔ x % p = y % p := by
  rw [← ofNat_eq_natCast, ← ofNat_eq_natCast]
  exact ofNat_ext_iff p

theorem natCast_emod (x : Nat) : ((x % p : Nat) : α) = (x : α) := by
  rw [natCast_ext_iff p, Nat.mod_mod]

theorem ofNat_emod (x : Nat) : OfNat.ofNat (α := α) (x % p) = OfNat.ofNat x := by
  rw [ofNat_eq_natCast, ofNat_eq_natCast]
  exact natCast_emod p x

theorem natCast_eq_zero_iff_of_lt {x : Nat} (h : x < p) : (x : α) = 0 ↔ x = 0 := by
  rw [natCast_eq_zero_iff p, Nat.mod_eq_of_lt h]

theorem natCast_eq_iff_of_lt {x y : Nat} (h₁ : x < p) (h₂ : y < p) :
    (x : α) = (y : α) ↔ x = y := by
  rw [natCast_ext_iff p, Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂]

end Semiring

section Ring

variable (p)  {α : Type u} [Ring α] [IsCharP α p]

private theorem mk'_aux {x y : Nat} (p : Nat) (h : y ≤ x) :
    (x - y) % p = 0 ↔ ∃ k₁ k₂, x + k₁ * p = y + k₂ * p := by
  rw [Nat.mod_eq_iff]
  by_cases h : p = 0
  · simp [h]
    omega
  · have h' : 0 < p := by omega
    simp [h, h']
    constructor
    · rintro ⟨k, h⟩
      refine ⟨0, k, ?_⟩
      simp [Nat.mul_comm]
      omega
    · rintro ⟨k₁, k₂, h⟩
      have : k₁ * p ≤ k₂ * p := by omega
      have : k₁ ≤ k₂ := Nat.le_of_mul_le_mul_right this h'
      refine ⟨k₂ - k₁, ?_⟩
      simp [Nat.mul_sub, Nat.mul_comm p k₁, Nat.mul_comm p k₂]
      omega

/-- Alternative constructor when `α` is a `Ring`. -/
def mk' (p : Nat) (α : Type u) [Ring α]
    (ofNat_eq_zero_iff : ∀ (x : Nat), OfNat.ofNat (α := α) x = 0 ↔ x % p = 0) : IsCharP α p where
  ofNat_ext_iff {x y} := by
    rw [← sub_eq_zero_iff]
    rw [Nat.mod_eq_mod_iff]
    by_cases h : y ≤ x
    · have : OfNat.ofNat (α := α) x - OfNat.ofNat y = OfNat.ofNat (x - y) := by rw [ofNat_sub h]
      rw [this, ofNat_eq_zero_iff]
      apply mk'_aux _ h
    · have : OfNat.ofNat (α := α) x - OfNat.ofNat (α := α) y = - OfNat.ofNat (y - x) := by rw [neg_ofNat_sub (by omega)]
      rw [this, neg_eq_zero, ofNat_eq_zero_iff]
      rw [mk'_aux _ (by omega)]
      rw [exists_comm]
      apply exists_congr
      intro k₁
      apply exists_congr
      intro k₂
      simp [eq_comm]

theorem intCast_eq_zero_iff (x : Int) : (x : α) = 0 ↔ x % p = 0 :=
  match x with
  | (x : Nat) => by
    have := ofNat_eq_zero_iff (α := α) p (x := x)
    rw [Int.ofNat_mod_ofNat, intCast_natCast, ← ofNat_eq_natCast]
    norm_cast
  | -(x + 1 : Nat) => by
    rw [Int.neg_emod, Int.ofNat_mod_ofNat, intCast_neg, intCast_natCast, neg_eq_zero]
    have := ofNat_eq_zero_iff (α := α) p (x := x + 1)
    rw [ofNat_eq_natCast] at this
    rw [this]
    simp only [Int.ofNat_dvd]
    simp only [← Nat.dvd_iff_mod_eq_zero, Int.natAbs_natCast,
      ite_eq_left_iff]
    by_cases h : p ∣ x + 1
    · simp [h]
    · simp only [h, not_false_eq_true,
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

theorem intCast_emod (x : Int) : ((x % p : Int) : α) = (x : α) := by
  rw [intCast_ext_iff p, Int.emod_emod]

end Ring

end IsCharP

theorem no_int_zero_divisors {α : Type u} [IntModule α] [NoNatZeroDivisors α] {k : Int} {a : α}
    : k ≠ 0 → k * a = 0 → a = 0 := by
  match k with
  | (k : Nat) =>
    simp only [ne_eq, Int.natCast_eq_zero]
    intro h₁ h₂
    replace h₁ : k ≠ 0 := by intro h; simp [h] at h₁
    rw [IntModule.hmul_nat] at h₂
    exact NoNatZeroDivisors.eq_zero_of_mul_eq_zero h₁ h₂
  | -(k+1 : Nat) =>
    rw [IntModule.neg_hmul]
    intro _ h
    replace h := congrArg (-·) h
    dsimp only at h
    rw [IntModule.neg_neg, IntModule.neg_zero] at h
    rw [IntModule.hmul_nat] at h
    exact NoNatZeroDivisors.eq_zero_of_mul_eq_zero (Nat.succ_ne_zero _) h

end Lean.Grind
