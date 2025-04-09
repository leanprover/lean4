/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Zero
import Init.Data.Int.DivMod.Lemmas
import Init.TacticsExtra

/-!
# A monolithic commutative ring typeclass for internal use in `grind`.
-/

namespace Lean.Grind

class CommRing (α : Type u) [∀ n, OfNat α n] extends Add α, Mul α, Neg α, Sub α, HPow α Nat α where
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
  ofNat_add : ∀ a b : Nat, OfNat.ofNat (α := α) (a + b) = OfNat.ofNat a + OfNat.ofNat b := by intros; rfl
  ofNat_mul : ∀ a b : Nat, OfNat.ofNat (α := α) (a * b) = OfNat.ofNat a * OfNat.ofNat b := by intros; rfl

namespace CommRing

variable {α : Type u} [∀ n, OfNat α n]

instance : NatCast α where
  natCast n := OfNat.ofNat n

theorem natCast_zero : ((0 : Nat) : α) = 0 := rfl

variable [CommRing α]

theorem natCast_succ (n : Nat) : ((n + 1 : Nat) : α) = ((n : α) + 1) := ofNat_add _ _

theorem zero_add (a : α) : 0 + a = a := by
  rw [add_comm, add_zero]

theorem add_neg_cancel (a : α) : a + -a = 0 := by
  rw [add_comm, neg_add_cancel]

theorem one_mul (a : α) : 1 * a = a := by
  rw [mul_comm, mul_one]

theorem right_distrib (a b c : α) : (a + b) * c = a * c + b * c := by
  rw [mul_comm, left_distrib, mul_comm c, mul_comm c]

theorem mul_zero (a : α) : a * 0 = 0 := by
  rw [mul_comm, zero_mul]

theorem add_left_inj {a b : α} (c : α) : a + c = b + c ↔ a = b :=
  ⟨fun h => by simpa [add_assoc, add_neg_cancel, add_zero] using (congrArg (· + -c) h),
   fun g => congrArg (· + c) g⟩

theorem add_right_inj (a b c : α) : a + b = a + c ↔ b = c := by
  rw [add_comm a b, add_comm a c, add_left_inj]

theorem neg_zero : (-0 : α) = 0 := by
  rw [← add_left_inj 0, neg_add_cancel, add_zero]

theorem neg_neg (a : α) : -(-a) = a := by
  rw [← add_left_inj (-a), neg_add_cancel, add_neg_cancel]

theorem neg_add (a b : α) : -(a + b) = -a + -b := by
  rw [← add_left_inj (a + b), neg_add_cancel, add_assoc (-a), add_comm a b, ← add_assoc (-b),
    neg_add_cancel, zero_add, neg_add_cancel]

theorem neg_sub (a b : α) : -(a - b) = b - a := by
  rw [sub_eq_add_neg, neg_add, neg_neg, sub_eq_add_neg, add_comm]

theorem sub_self (a : α) : a - a = 0 := by
  rw [sub_eq_add_neg, add_neg_cancel]

instance : IntCast α where
  intCast n := match n with
  | Int.ofNat n => OfNat.ofNat n
  | Int.negSucc n => -OfNat.ofNat (n + 1)

theorem intCast_zero : ((0 : Int) : α) = 0 := rfl
theorem intCast_one : ((1 : Int) : α) = 1 := rfl
theorem intCast_neg_one : ((-1 : Int) : α) = -1 := rfl
theorem intCast_ofNat (n : Nat) : ((n : Int) : α) = (n : α) := rfl
theorem intCast_ofNat_add_one (n : Nat) : ((n + 1 : Int) : α) = (n : α) + 1 := ofNat_add _ _
theorem intCast_negSucc (n : Nat) : ((-(n + 1) : Int) : α) = -((n : α) + 1) := congrArg (- ·) (ofNat_add _ _)
theorem intCast_neg (x : Int) : ((-x : Int) : α) = - (x : α) :=
  match x with
  | (0 : Nat) => neg_zero.symm
  | (n + 1 : Nat) => by
    rw [Int.natCast_add, Int.cast_ofNat_Int, intCast_negSucc, intCast_ofNat_add_one]
  | -((n : Nat) + 1) => by
    rw [Int.neg_neg, intCast_ofNat_add_one, intCast_negSucc, neg_neg]
theorem intCast_nat_add {x y : Nat} : ((x + y : Int) : α) = ((x : α) + (y : α)) := ofNat_add _ _
theorem intCast_nat_sub {x y : Nat} (h : x ≥ y) : (((x - y : Nat) : Int) : α) = ((x : α) - (y : α)) := by
  induction x with
  | zero =>
    have : y = 0 := by omega
    simp [this, intCast_zero, natCast_zero, sub_eq_add_neg, zero_add, neg_zero]
  | succ x ih =>
    by_cases h : x + 1 = y
    · simp [h, intCast_zero, sub_self]
    · have : ((x + 1 - y : Nat) : Int) = (x - y : Nat) + 1 := by omega
      rw [this, intCast_ofNat_add_one]
      specialize ih (by omega)
      rw [intCast_ofNat] at ih
      rw [ih, natCast_succ, sub_eq_add_neg, sub_eq_add_neg, add_assoc, add_comm _ 1, ← add_assoc]
theorem intCast_add (x y : Int) : ((x + y : Int) : α) = ((x : α) + (y : α)) :=
  match x, y with
  | (x : Nat), (y : Nat) => ofNat_add _ _
  | (x : Nat), (-(y + 1 : Nat)) => by
    by_cases h : x ≥ y + 1
    · have : (x + -(y+1 : Nat) : Int) = ((x - (y + 1) : Nat) : Int) := by omega
      rw [this, intCast_neg, intCast_nat_sub h, intCast_ofNat, intCast_ofNat, sub_eq_add_neg]
    · have : (x + -(y+1 : Nat) : Int) = (-(y + 1 - x : Nat) : Int) := by omega
      rw [this, intCast_neg, intCast_nat_sub (by omega), intCast_ofNat, intCast_neg, intCast_ofNat,
        neg_sub, sub_eq_add_neg]
  | (-(x + 1 : Nat)), (y : Nat) => by
    sorry
  | (-(x + 1 : Nat)), (-(y + 1 : Nat)) => by
    rw [← Int.neg_add, intCast_neg, intCast_nat_add, neg_add, intCast_neg, intCast_neg, intCast_ofNat, intCast_ofNat]
theorem intCast_mul (x y : Int) : ((x * y : Int) : α) = ((x : α) * (y : α)) := rfl

end CommRing

open CommRing

class IsCharP (α : Type u) [∀ n, OfNat α n] [CommRing α] (p : outParam Nat) where
  char (p) : ∀ {x : Nat}, OfNat.ofNat (α := α) x = 0 ↔ x % p = 0

namespace IsCharP

variable {α : Type u} [∀ n, OfNat α n] [CommRing α] [IsCharP α p]

theorem ext_iff {x y : Nat} : OfNat.ofNat (α := α) x = OfNat.ofNat (α := α) y ↔ x % p = y % p := by
  constructor
  · intro h
    apply Int.ofNat_inj.mp
    simp
    apply Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr

    replace h : ((x - y : Int) : α) = 0 := by rw [cast_sub, h, add_neg_cancel]
    exact Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr ((IsCharP.char p).mp h)
  · intro h
    have : ((x - y : Int) : α) = 0 :=
      (IsCharP.char p).mpr (by rw [Int.sub_emod, h, Int.sub_self, Int.zero_emod])
    replace this := congrArg (· + (y : α)) this
    simpa [cast_sub, zero_add, add_assoc, neg_add_cancel, add_zero] using this

-- theorem ext {x y : Int} (h : x % p = y % p) : (x : α) = (y : α) := ext_iff.mpr h

-- theorem cast_emod (x : Int) : ((x % p : Int) : α) = (x : α) := by
--   rw [ext_iff, Int.emod_emod]

-- theorem eq_zero_iff_of_lt {x : Int} (h₁ : 0 ≤ x) (h₂ : x < p) : (x : α) = 0 ↔ x = 0 := by
--   rw [IsCharP.char, Int.emod_eq_of_lt h₁ h₂]

-- theorem eq_iff_of_lt {x y : Int} (h₁ : 0 ≤ x) (h₂ : x < p) (h₃ : 0 ≤ y) (h₄ : y < p) :
--     (x : α) = (y : α) ↔ x = y := by
--   rw [ext_iff, Int.emod_eq_of_lt h₁ h₂, Int.emod_eq_of_lt h₃ h₄]

end IsCharP

end Lean.Grind
