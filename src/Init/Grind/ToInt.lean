/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude

import Init.Data.Int.DivMod.Basic
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Fin.Lemmas
import Init.Data.UInt.Lemmas
import Init.Data.SInt.Lemmas

/-!
# Typeclasses for types that can be embedded into an interval of `Int`.

The typeclass `ToInt α lo? hi?` carries the data of a function `ToInt.toInt : α → Int`
which is injective, lands between the (optional) lower and upper bounds `lo?` and `hi?`.

The function `ToInt.wrap` is the identity if either bound is `none`,
and otherwise wraps the integers into the interval `[lo, hi)`.

The typeclass `ToInt.Add α lo? hi?` then asserts that `toInt (x + y) = wrap lo? hi? (toInt x + toInt y)`.
There are many variants for other operations.

These typeclasses are used solely in the `grind` tactic to lift linear inequalities into `Int`.

-- TODO: instances for `ToInt.Mod` (only exists for `Fin n` so far)
-- TODO: typeclasses for LT, and other algebraic operations.
-- TODO: typeclasses for `BitVec v` and `ISize`.
-/

namespace Lean.Grind

class ToInt (α : Type u) (lo? hi? : outParam (Option Int)) where
  toInt : α → Int
  toInt_inj : ∀ x y, toInt x = toInt y → x = y
  le_toInt : lo? = some lo → lo ≤ toInt x
  toInt_lt : hi? = some hi → toInt x < hi

@[simp]
def ToInt.wrap (lo? hi? : Option Int) (x : Int) : Int :=
  match lo?, hi? with
  | some lo, some hi => (x - lo) % (hi - lo) + lo
  | _, _ => x

class ToInt.Add (α : Type u) [Add α] (lo? hi? : Option Int) [ToInt α lo? hi?] where
  toInt_add : ∀ x y : α, toInt (x + y) = wrap lo? hi? (toInt x + toInt y)

class ToInt.Mod (α : Type u) [Mod α] (lo? hi? : Option Int) [ToInt α lo? hi?] where
  toInt_mod : ∀ x y : α, toInt (x % y) = wrap lo? hi? (toInt x % toInt y)

class ToInt.LE (α : Type u) [LE α] (lo? hi? : Option Int) [ToInt α lo? hi?] where
  le_iff : ∀ x y : α, x ≤ y ↔ toInt x ≤ toInt y

instance : ToInt Int none none where
  toInt := id
  toInt_inj := by simp
  le_toInt := by simp
  toInt_lt := by simp

@[simp] theorem toInt_int (x : Int) : ToInt.toInt x = x := rfl

instance : ToInt.Add Int none none where
  toInt_add := by simp

instance : ToInt.LE Int none none where
  le_iff x y := by simp

instance : ToInt Nat (some 0) none where
  toInt := Nat.cast
  toInt_inj x y := Int.ofNat_inj.mp
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x
  toInt_lt := by simp

@[simp] theorem toInt_nat (x : Nat) : ToInt.toInt x = (x : Int) := rfl

instance : ToInt.Add Nat (some 0) none where
  toInt_add := by simp

instance : ToInt.LE Nat (some 0) none where
  le_iff x y := by simp

-- Mathlib will add a `ToInt ℕ+ (some 1) none` instance.

instance : ToInt (Fin n) (some 0) (some n) where
  toInt x := x.val
  toInt_inj x y w := Fin.eq_of_val_eq (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp only [Option.some.injEq] at w; subst w; exact Int.natCast_nonneg x
  toInt_lt {hi x} w := by simp only [Option.some.injEq] at w; subst w; exact Int.ofNat_lt.mpr x.isLt

@[simp] theorem toInt_fin (x : Fin n) : ToInt.toInt x = (x.val : Int) := rfl

instance : ToInt.Add (Fin n) (some 0) (some n) where
  toInt_add x y := by rfl

instance : ToInt.Mod (Fin n) (some 0) (some n) where
  toInt_mod x y := by
    simp only [toInt_fin, Fin.mod_val, Int.natCast_emod, ToInt.wrap, Int.sub_zero, Int.add_zero]
    rw [Int.emod_eq_of_lt (b := n)]
    · omega
    · rw [Int.ofNat_mod_ofNat, ← Fin.mod_val]
      exact Int.ofNat_lt.mpr (x % y).isLt

instance : ToInt.LE (Fin n) (some 0) (some n) where
  le_iff x y := by simpa using Fin.le_def

instance : ToInt UInt8 (some 0) (some (2^8)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt8.toNat_inj.mp (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by simp at w; subst w; exact Int.lt_toNat.mp (UInt8.toNat_lt x)

@[simp] theorem toInt_uint8 (x : UInt8) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add UInt8 (some 0) (some (2^8)) where
  toInt_add x y := by simp

instance : ToInt.LE UInt8 (some 0) (some (2^8)) where
  le_iff x y := by simpa using UInt8.le_iff_toBitVec_le

instance : ToInt UInt16 (some 0) (some (2^16)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt16.toNat_inj.mp (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by simp at w; subst w; exact Int.lt_toNat.mp (UInt16.toNat_lt x)

@[simp] theorem toInt_uint16 (x : UInt16) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add UInt16 (some 0) (some (2^16)) where
  toInt_add x y := by simp

instance : ToInt.LE UInt16 (some 0) (some (2^16)) where
  le_iff x y := by simpa using UInt16.le_iff_toBitVec_le

instance : ToInt UInt32 (some 0) (some (2^32)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt32.toNat_inj.mp (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by simp at w; subst w; exact Int.lt_toNat.mp (UInt32.toNat_lt x)

@[simp] theorem toInt_uint32 (x : UInt32) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add UInt32 (some 0) (some (2^32)) where
  toInt_add x y := by simp

instance : ToInt.LE UInt32 (some 0) (some (2^32)) where
  le_iff x y := by simpa using UInt32.le_iff_toBitVec_le

instance : ToInt UInt64 (some 0) (some (2^64)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt64.toNat_inj.mp (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by simp at w; subst w; exact Int.lt_toNat.mp (UInt64.toNat_lt x)

@[simp] theorem toInt_uint64 (x : UInt64) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add UInt64 (some 0) (some (2^64)) where
  toInt_add x y := by simp

instance : ToInt.LE UInt64 (some 0) (some (2^64)) where
  le_iff x y := by simpa using UInt64.le_iff_toBitVec_le

instance : ToInt USize (some 0) (some (2^System.Platform.numBits)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := USize.toNat_inj.mp (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by
    simp at w; subst w
    rw [show (2 : Int) ^ System.Platform.numBits = (2 ^ System.Platform.numBits : Nat) by simp,
      Int.ofNat_lt]
    exact USize.toNat_lt_two_pow_numBits x

@[simp] theorem toInt_usize (x : USize) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add USize (some 0) (some (2^System.Platform.numBits)) where
  toInt_add x y := by simp

instance : ToInt.LE USize (some 0) (some (2^System.Platform.numBits)) where
  le_iff x y := by simpa using USize.le_iff_toBitVec_le

instance : ToInt Int8 (some (-2^7)) (some (2^7)) where
  toInt x := x.toInt
  toInt_inj x y w := Int8.toInt_inj.mp w
  le_toInt {lo x} w := by simp at w; subst w; exact Int8.le_toInt x
  toInt_lt {hi x} w := by simp at w; subst w; exact Int8.toInt_lt x

@[simp] theorem toInt_int8 (x : Int8) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Add Int8 (some (-2^7)) (some (2^7)) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.LE Int8 (some (-2^7)) (some (2^7)) where
  le_iff x y := by simpa using Int8.le_iff_toInt_le

instance : ToInt Int16 (some (-2^15)) (some (2^15)) where
  toInt x := x.toInt
  toInt_inj x y w := Int16.toInt_inj.mp w
  le_toInt {lo x} w := by simp at w; subst w; exact Int16.le_toInt x
  toInt_lt {hi x} w := by simp at w; subst w; exact Int16.toInt_lt x

@[simp] theorem toInt_int16 (x : Int16) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Add Int16 (some (-2^15)) (some (2^15)) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.LE Int16 (some (-2^15)) (some (2^15)) where
  le_iff x y := by simpa using Int16.le_iff_toInt_le

instance : ToInt Int32 (some (-2^31)) (some (2^31)) where
  toInt x := x.toInt
  toInt_inj x y w := Int32.toInt_inj.mp w
  le_toInt {lo x} w := by simp at w; subst w; exact Int32.le_toInt x
  toInt_lt {hi x} w := by simp at w; subst w; exact Int32.toInt_lt x

@[simp] theorem toInt_int32 (x : Int32) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Add Int32 (some (-2^31)) (some (2^31)) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.LE Int32 (some (-2^31)) (some (2^31)) where
  le_iff x y := by simpa using Int32.le_iff_toInt_le

instance : ToInt Int64 (some (-2^63)) (some (2^63)) where
  toInt x := x.toInt
  toInt_inj x y w := Int64.toInt_inj.mp w
  le_toInt {lo x} w := by simp at w; subst w; exact Int64.le_toInt x
  toInt_lt {hi x} w := by simp at w; subst w; exact Int64.toInt_lt x

@[simp] theorem toInt_int64 (x : Int64) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Add Int64 (some (-2^63)) (some (2^63)) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.LE Int64 (some (-2^63)) (some (2^63)) where
  le_iff x y := by simpa using Int64.le_iff_toInt_le

-- TODO:
-- instance [NeZero v] : ToInt (BitVec v) (some (-2^(v-1))) (some (2^(v-1))) := sorry
-- instance : ToInt ISize (some (-2^(System.Platform.numBits-1))) (some (2^(System.Platform.numBits-1))) := sorry

end Lean.Grind
