/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import all Init.Grind.ToInt
import Init.Data.Int.DivMod.Basic
import Init.Data.Int.Lemmas
import Init.Data.Int.Order
import Init.Data.Fin.Lemmas
import Init.Data.UInt.Lemmas
import Init.Data.SInt.Lemmas

namespace Lean.Grind

/-! ## Instances for concrete types-/

instance : ToInt Int none none where
  toInt := id
  toInt_inj := by simp
  le_toInt := by simp
  toInt_lt := by simp

@[simp] theorem toInt_int (x : Int) : ToInt.toInt x = x := rfl

instance : ToInt.Add Int none none where
  toInt_add := by simp

instance : ToInt.Neg Int none none where
  toInt_neg x := by simp

instance : ToInt.Sub Int none none where
  toInt_sub x y := by simp

instance : ToInt.Mod Int none none where
  toInt_mod x y := by simp

instance : ToInt.LE Int none none where
  le_iff x y := by simp

instance : ToInt.LT Int none none where
  lt_iff x y := by simp

instance : ToInt Nat (some 0) none where
  toInt := Nat.cast
  toInt_inj x y := Int.ofNat_inj.mp
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x
  toInt_lt := by simp

@[simp] theorem toInt_nat (x : Nat) : ToInt.toInt x = (x : Int) := rfl

instance : ToInt.Add Nat (some 0) none where
  toInt_add := by simp

instance : ToInt.Mod Nat (some 0) none where
  toInt_mod x y := by simp

instance : ToInt.LE Nat (some 0) none where
  le_iff x y := by simp

instance : ToInt.LT Nat (some 0) none where
  lt_iff x y := by simp

-- Mathlib will add a `ToInt ℕ+ (some 1) none` instance.

instance : ToInt (Fin n) (some 0) (some n) where
  toInt x := x.val
  toInt_inj x y w := Fin.eq_of_val_eq (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp only [Option.some.injEq] at w; subst w; exact Int.natCast_nonneg x
  toInt_lt {hi x} w := by simp only [Option.some.injEq] at w; subst w; exact Int.ofNat_lt.mpr x.isLt

@[simp] theorem toInt_fin (x : Fin n) : ToInt.toInt x = (x.val : Int) := rfl

instance : ToInt.Add (Fin n) (some 0) (some n) where
  toInt_add x y := by rfl

instance [NeZero n] : ToInt.Zero (Fin n) (some 0) (some n) where
  toInt_zero := by rfl

-- The `ToInt.Neg` and `ToInt.Sub` instances are generated automatically from the `IntModule (Fin n)` instance.

instance : ToInt.Mod (Fin n) (some 0) (some n) where
  toInt_mod x y := by
    simp only [toInt_fin, Fin.mod_val, Int.natCast_emod]

instance : ToInt.LE (Fin n) (some 0) (some n) where
  le_iff x y := by simpa using Fin.le_def

instance : ToInt.LT (Fin n) (some 0) (some n) where
  lt_iff x y := by simpa using Fin.lt_def

instance : ToInt UInt8 (some 0) (some (2^8)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt8.toNat_inj.mp (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by simp at w; subst w; exact Int.lt_toNat.mp (UInt8.toNat_lt x)

@[simp] theorem toInt_uint8 (x : UInt8) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add UInt8 (some 0) (some (2^8)) where
  toInt_add x y := by simp

instance : ToInt.Zero UInt8 (some 0) (some (2^8)) where
  toInt_zero := by simp

instance : ToInt.Mod UInt8 (some 0) (some (2^8)) where
  toInt_mod x y := by simp

instance : ToInt.LE UInt8 (some 0) (some (2^8)) where
  le_iff x y := by simpa using UInt8.le_iff_toBitVec_le

instance : ToInt.LT UInt8 (some 0) (some (2^8)) where
  lt_iff x y := by simpa using UInt8.lt_iff_toBitVec_lt

instance : ToInt UInt16 (some 0) (some (2^16)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt16.toNat_inj.mp (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by simp at w; subst w; exact Int.lt_toNat.mp (UInt16.toNat_lt x)

@[simp] theorem toInt_uint16 (x : UInt16) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add UInt16 (some 0) (some (2^16)) where
  toInt_add x y := by simp

instance : ToInt.Zero UInt16 (some 0) (some (2^16)) where
  toInt_zero := by simp

instance : ToInt.Mod UInt16 (some 0) (some (2^16)) where
  toInt_mod x y := by simp

instance : ToInt.LE UInt16 (some 0) (some (2^16)) where
  le_iff x y := by simpa using UInt16.le_iff_toBitVec_le

instance : ToInt.LT UInt16 (some 0) (some (2^16)) where
  lt_iff x y := by simpa using UInt16.lt_iff_toBitVec_lt

instance : ToInt UInt32 (some 0) (some (2^32)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt32.toNat_inj.mp (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by simp at w; subst w; exact Int.lt_toNat.mp (UInt32.toNat_lt x)

@[simp] theorem toInt_uint32 (x : UInt32) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add UInt32 (some 0) (some (2^32)) where
  toInt_add x y := by simp

instance : ToInt.Zero UInt32 (some 0) (some (2^32)) where
  toInt_zero := by simp

instance : ToInt.Mod UInt32 (some 0) (some (2^32)) where
  toInt_mod x y := by simp

instance : ToInt.LE UInt32 (some 0) (some (2^32)) where
  le_iff x y := by simpa using UInt32.le_iff_toBitVec_le

instance : ToInt.LT UInt32 (some 0) (some (2^32)) where
  lt_iff x y := by simpa using UInt32.lt_iff_toBitVec_lt

instance : ToInt UInt64 (some 0) (some (2^64)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt64.toNat_inj.mp (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by simp at w; subst w; exact Int.lt_toNat.mp (UInt64.toNat_lt x)

@[simp] theorem toInt_uint64 (x : UInt64) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add UInt64 (some 0) (some (2^64)) where
  toInt_add x y := by simp

instance : ToInt.Zero UInt64 (some 0) (some (2^64)) where
  toInt_zero := by simp

instance : ToInt.Mod UInt64 (some 0) (some (2^64)) where
  toInt_mod x y := by simp

instance : ToInt.LE UInt64 (some 0) (some (2^64)) where
  le_iff x y := by simpa using UInt64.le_iff_toBitVec_le

instance : ToInt.LT UInt64 (some 0) (some (2^64)) where
  lt_iff x y := by simpa using UInt64.lt_iff_toBitVec_lt

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

instance : ToInt.Zero USize (some 0) (some (2^System.Platform.numBits)) where
  toInt_zero := by simp

instance : ToInt.Mod USize (some 0) (some (2^System.Platform.numBits)) where
  toInt_mod x y := by simp

instance : ToInt.LE USize (some 0) (some (2^System.Platform.numBits)) where
  le_iff x y := by simpa using USize.le_iff_toBitVec_le

instance : ToInt.LT USize (some 0) (some (2^System.Platform.numBits)) where
  lt_iff x y := by simpa using USize.lt_iff_toBitVec_lt

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

instance : ToInt.Zero Int8 (some (-2^7)) (some (2^7)) where
  toInt_zero := by
    --  simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int8).toInt = _
    rw [Int8.toInt_zero]
    decide

-- Note that we can not define `ToInt.Mod` instances for `Int8`,
-- because the condition does not hold unless `0 ≤ x.toInt ∨ y.toInt ∣ x.toInt ∨ y = 0`.

instance : ToInt.LE Int8 (some (-2^7)) (some (2^7)) where
  le_iff x y := by simpa using Int8.le_iff_toInt_le

instance : ToInt.LT Int8 (some (-2^7)) (some (2^7)) where
  lt_iff x y := by simpa using Int8.lt_iff_toInt_lt

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

instance : ToInt.Zero Int16 (some (-2^15)) (some (2^15)) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int16).toInt = _
    rw [Int16.toInt_zero]
    decide

instance : ToInt.LE Int16 (some (-2^15)) (some (2^15)) where
  le_iff x y := by simpa using Int16.le_iff_toInt_le

instance : ToInt.LT Int16 (some (-2^15)) (some (2^15)) where
  lt_iff x y := by simpa using Int16.lt_iff_toInt_lt

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

instance : ToInt.Zero Int32 (some (-2^31)) (some (2^31)) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int32).toInt = _
    rw [Int32.toInt_zero]
    decide

instance : ToInt.LE Int32 (some (-2^31)) (some (2^31)) where
  le_iff x y := by simpa using Int32.le_iff_toInt_le

instance : ToInt.LT Int32 (some (-2^31)) (some (2^31)) where
  lt_iff x y := by simpa using Int32.lt_iff_toInt_lt

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

instance : ToInt.Zero Int64 (some (-2^63)) (some (2^63)) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int64).toInt = _
    rw [Int64.toInt_zero]
    decide

instance : ToInt.LE Int64 (some (-2^63)) (some (2^63)) where
  le_iff x y := by simpa using Int64.le_iff_toInt_le

instance : ToInt.LT Int64 (some (-2^63)) (some (2^63)) where
  lt_iff x y := by simpa using Int64.lt_iff_toInt_lt

instance : ToInt (BitVec v) (some 0) (some (2^v)) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w :=
    BitVec.eq_of_toNat_eq (Int.ofNat_inj.mp w)
  le_toInt {lo x} w := by simp at w; subst w; exact Int.natCast_nonneg x.toNat
  toInt_lt {hi x} w := by
    simp at w; subst w;
    simpa using Int.ofNat_lt.mpr (BitVec.isLt x)

@[simp] theorem toInt_bitVec (x : BitVec v) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Add (BitVec v) (some 0) (some (2^v)) where
  toInt_add x y := by simp

instance : ToInt.Zero (BitVec v) (some 0) (some (2^v)) where
  toInt_zero := by simp

instance : ToInt.Mod (BitVec v) (some 0) (some (2^v)) where
  toInt_mod x y := by simp

instance : ToInt.LE (BitVec v) (some 0) (some (2^v)) where
  le_iff x y := by simpa using BitVec.le_def

instance : ToInt.LT (BitVec v) (some 0) (some (2^v)) where
  lt_iff x y := by simpa using BitVec.lt_def

instance : ToInt ISize (some (-2^(System.Platform.numBits-1))) (some (2^(System.Platform.numBits-1))) where
  toInt x := x.toInt
  toInt_inj x y w := ISize.toInt_inj.mp w
  le_toInt {lo x} w := by simp at w; subst w; exact ISize.two_pow_numBits_le_toInt x
  toInt_lt {hi x} w := by simp at w; subst w; exact ISize.toInt_lt_two_pow_numBits x

@[simp] theorem toInt_isize (x : ISize) : ToInt.toInt x = x.toInt := rfl

instance : ToInt.Add ISize (some (-2^(System.Platform.numBits-1))) (some (2^(System.Platform.numBits-1))) where
  toInt_add x y := by
    rw [toInt_isize, ISize.toInt_add, ToInt.wrap_eq_bmod (Int.pow_nonneg (by decide))]
    have p₁ : (2 : Int) * 2 ^ (System.Platform.numBits - 1) = 2 ^ System.Platform.numBits := by
      have := System.Platform.numBits_pos
      have : System.Platform.numBits - 1 + 1 = System.Platform.numBits := by omega
      simp [← Int.pow_succ', this]
    have p₂ : ((2 : Int) ^ System.Platform.numBits).toNat = 2 ^ System.Platform.numBits := by
      rw [Int.toNat_pow_of_nonneg (by decide)]
      simp
    simp [p₁, p₂]

instance : ToInt.Zero ISize (some (-2^(System.Platform.numBits-1))) (some (2^(System.Platform.numBits-1))) where
  toInt_zero := by
    rw [toInt_isize]
    rw [ISize.toInt_zero, ToInt.wrap_eq_bmod (Int.pow_nonneg (by decide))]
    simp

instance instToIntLEISize : ToInt.LE ISize (some (-2^(System.Platform.numBits-1))) (some (2^(System.Platform.numBits-1))) where
  le_iff x y := by simpa using ISize.le_iff_toInt_le

instance instToIntLTISize : ToInt.LT ISize (some (-2^(System.Platform.numBits-1))) (some (2^(System.Platform.numBits-1))) where
  lt_iff x y := by simpa using ISize.lt_iff_toInt_lt

end Lean.Grind
