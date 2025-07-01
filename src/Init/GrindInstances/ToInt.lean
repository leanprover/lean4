/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import all Init.Grind.ToInt
public import Init.Grind.Module.Basic
public import Init.Grind.Ring.ToInt
public import Init.Data.Int.DivMod.Basic
public import Init.Data.Int.Lemmas
public import Init.Data.Int.Order
public import Init.Data.Fin.Lemmas
public import Init.Data.UInt.Lemmas
public import Init.Data.SInt.Lemmas

public section

namespace Lean.Grind

/-! ## Instances for concrete types-/

instance : ToInt Int .ii where
  toInt := id
  toInt_inj := by simp
  toInt_mem := by simp

@[simp] theorem toInt_int (x : Int) : ToInt.toInt x = x := rfl

instance : ToInt.Zero Int .ii where
  toInt_zero := by simp

instance : ToInt.OfNat Int .ii where
  toInt_ofNat _ := by simp; rfl

instance : ToInt.Add Int .ii where
  toInt_add := by simp

instance : ToInt.Neg Int .ii where
  toInt_neg x := by simp

instance : ToInt.Sub Int .ii where
  toInt_sub x y := by simp

instance : ToInt.Mul Int .ii where
  toInt_mul x y := by simp

instance : ToInt.Pow Int .ii where
  toInt_pow x n := by simp

instance : ToInt.Mod Int .ii where
  toInt_mod x y := by simp

instance : ToInt.Div Int .ii where
  toInt_div x y := by simp

instance : ToInt.LE Int .ii where
  le_iff x y := by simp

instance : ToInt.LT Int .ii where
  lt_iff x y := by simp

instance : ToInt Nat (.ci 0) where
  toInt := Nat.cast
  toInt_inj x y := Int.ofNat_inj.mp
  toInt_mem := by simp

@[simp] theorem toInt_nat (x : Nat) : ToInt.toInt x = (x : Int) := rfl

instance : ToInt.Zero Nat (.ci 0) where
  toInt_zero := by simp

instance : ToInt.OfNat Nat (.ci 0) where
  toInt_ofNat _ := by simp; rfl

instance : ToInt.Add Nat (.ci 0) where
  toInt_add := by simp <;> omega

instance : ToInt.Mul Nat (.ci 0) where
  toInt_mul x y := by
    dsimp only [IntInterval.wrap]
    rw [Int.max_eq_left]
    simp only [toInt_nat, Int.natCast_mul]
    simp [toInt_nat, ← Int.natCast_mul]

instance : ToInt.Pow Nat (.ci 0) where
  toInt_pow x n := by
    dsimp only [IntInterval.wrap]
    rw [Int.max_eq_left]
    simp only [toInt_nat, Int.natCast_pow]
    simp [toInt_nat, ← Int.natCast_pow]

instance : ToInt.Sub Nat (.ci 0) where
  toInt_sub x y := by simp; omega

instance : ToInt.Mod Nat (.ci 0) where
  toInt_mod x y := by simp

instance : ToInt.Div Nat (.ci 0) where
  toInt_div x y := by simp

instance : ToInt.LE Nat (.ci 0) where
  le_iff x y := by simp

instance : ToInt.LT Nat (.ci 0) where
  lt_iff x y := by simp

-- Mathlib will add a `ToInt ℕ+ (some 1) none` instance.

instance : ToInt (Fin n) (.co 0 n) where
  toInt x := x.val
  toInt_inj x y w := Fin.eq_of_val_eq (Int.ofNat_inj.mp w)
  toInt_mem := by simp

@[simp] theorem toInt_fin (x : Fin n) : ToInt.toInt x = (x.val : Int) := rfl

instance [NeZero n] : ToInt.Zero (Fin n) (.co 0 n) where
  toInt_zero := rfl

instance [NeZero n] : ToInt.OfNat (Fin n) (.co 0 n) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add (Fin n) (.co 0 n) where
  toInt_add x y := by rfl

-- The `ToInt.Neg` and `ToInt.Sub` instances are generated automatically from the `IntModule (Fin n)` instance.
-- See `Init.GrindInstances.Ring.Fin`.

instance : ToInt.Mul (Fin n) (.co 0 n) where
  toInt_mul x y := by rfl

-- The `IoInt.Pow` instance is defined in `Init.GrindInstances.Ring.Fin`,
-- since the power operation is only defined there.

instance : ToInt.Mod (Fin n) (.co 0 n) where
  toInt_mod _ _ := rfl

instance : ToInt.Div (Fin n) (.co 0 n) where
  toInt_div _ _ := rfl

instance : ToInt.LE (Fin n) (.co 0 n) where
  le_iff x y := by simpa using Fin.le_def

instance : ToInt.LT (Fin n) (.co 0 n) where
  lt_iff x y := by simpa using Fin.lt_def

instance : ToInt UInt8 (.uint 8) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt8.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.lt_toNat.mp (UInt8.toNat_lt x)

@[simp] theorem toInt_uint8 (x : UInt8) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero UInt8 (.uint 8) where
  toInt_zero := by simp

instance : ToInt.OfNat UInt8 (.uint 8) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add UInt8 (.uint 8) where
  toInt_add x y := by simp

instance : ToInt.Mul UInt8 (.uint 8) where
  toInt_mul x y := by simp

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.UInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.Mod UInt8 (.uint 8) where
  toInt_mod x y := by simp

instance : ToInt.Div UInt8 (.uint 8) where
  toInt_div x y := by simp

instance : ToInt.LE UInt8 (.uint 8) where
  le_iff x y := by simpa using UInt8.le_iff_toBitVec_le

instance : ToInt.LT UInt8 (.uint 8) where
  lt_iff x y := by simpa using UInt8.lt_iff_toBitVec_lt

instance : ToInt UInt16 (.uint 16) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt16.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.lt_toNat.mp (UInt16.toNat_lt x)

@[simp] theorem toInt_uint16 (x : UInt16) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero UInt16 (.uint 16) where
  toInt_zero := by simp

instance : ToInt.OfNat UInt16 (.uint 16) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add UInt16 (.uint 16) where
  toInt_add x y := by simp

instance : ToInt.Mul UInt16 (.uint 16) where
  toInt_mul x y := by simp

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.UInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.Mod UInt16 (.uint 16) where
  toInt_mod x y := by simp

instance : ToInt.Div UInt16 (.uint 16) where
  toInt_div x y := by simp

instance : ToInt.LE UInt16 (.uint 16) where
  le_iff x y := by simpa using UInt16.le_iff_toBitVec_le

instance : ToInt.LT UInt16 (.uint 16) where
  lt_iff x y := by simpa using UInt16.lt_iff_toBitVec_lt

instance : ToInt UInt32 (.uint 32) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt32.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.lt_toNat.mp (UInt32.toNat_lt x)

@[simp] theorem toInt_uint32 (x : UInt32) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero UInt32 (.uint 32) where
  toInt_zero := by simp

instance : ToInt.OfNat UInt32 (.uint 32) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add UInt32 (.uint 32) where
  toInt_add x y := by simp

instance : ToInt.Mul UInt32 (.uint 32) where
  toInt_mul x y := by simp

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.UInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.Mod UInt32 (.uint 32) where
  toInt_mod x y := by simp

instance : ToInt.Div UInt32 (.uint 32) where
  toInt_div x y := by simp

instance : ToInt.LE UInt32 (.uint 32) where
  le_iff x y := by simpa using UInt32.le_iff_toBitVec_le

instance : ToInt.LT UInt32 (.uint 32) where
  lt_iff x y := by simpa using UInt32.lt_iff_toBitVec_lt

instance : ToInt UInt64 (.uint 64) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := UInt64.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.lt_toNat.mp (UInt64.toNat_lt x)

@[simp] theorem toInt_uint64 (x : UInt64) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero UInt64 (.uint 64) where
  toInt_zero := by simp

instance : ToInt.OfNat UInt64 (.uint 64) where
  toInt_ofNat x := by simp; rfl

instance : ToInt.Add UInt64 (.uint 64) where
  toInt_add x y := by simp

instance : ToInt.Mul UInt64 (.uint 64) where
  toInt_mul x y := by simp

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.UInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.Mod UInt64 (.uint 64) where
  toInt_mod x y := by simp

instance : ToInt.Div UInt64 (.uint 64) where
  toInt_div x y := by simp

instance : ToInt.LE UInt64 (.uint 64) where
  le_iff x y := by simpa using UInt64.le_iff_toBitVec_le

instance : ToInt.LT UInt64 (.uint 64) where
  lt_iff x y := by simpa using UInt64.lt_iff_toBitVec_lt

instance : ToInt USize (.uint System.Platform.numBits) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w := USize.toNat_inj.mp (Int.ofNat_inj.mp w)
  toInt_mem x := by
    simp only [IntInterval.mem_co, Int.ofNat_zero_le, true_and]
    rw [show (2 : Int) ^ System.Platform.numBits = (2 ^ System.Platform.numBits : Nat) by simp,
      Int.ofNat_lt]
    exact USize.toNat_lt_two_pow_numBits x

@[simp] theorem toInt_usize (x : USize) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero USize (.uint System.Platform.numBits) where
  toInt_zero := by simp

instance : ToInt.OfNat USize (.uint System.Platform.numBits) where
  toInt_ofNat x := by
    change ((x % 2^System.Platform.numBits : Nat) : Int) = _
    simp

instance : ToInt.Add USize (.uint System.Platform.numBits) where
  toInt_add x y := by simp

instance : ToInt.Mul USize (.uint System.Platform.numBits) where
  toInt_mul x y := by simp

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.UInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.Mod USize (.uint System.Platform.numBits) where
  toInt_mod x y := by simp

instance : ToInt.Div USize (.uint System.Platform.numBits) where
  toInt_div x y := by simp

instance : ToInt.LE USize (.uint System.Platform.numBits) where
  le_iff x y := by simpa using USize.le_iff_toBitVec_le

instance : ToInt.LT USize (.uint System.Platform.numBits) where
  lt_iff x y := by simpa using USize.lt_iff_toBitVec_lt

instance : ToInt Int8 (.sint 8) where
  toInt x := x.toInt
  toInt_inj x y w := Int8.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨Int8.le_toInt x, Int8.toInt_lt x⟩

@[simp] theorem toInt_int8 (x : Int8) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Zero Int8 (.sint 8) where
  toInt_zero := by
    --  simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int8).toInt = _
    rw [Int8.toInt_zero]

instance : ToInt.OfNat Int8 (.sint 8) where
  toInt_ofNat x := by
    rw [toInt_int8, Int8.toInt_ofNat, Int8.size, Int.bmod_eq_emod, IntInterval.wrap]
    simp
    split <;> omega

instance : ToInt.Add Int8 (.sint 8) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.Mul Int8 (.sint 8) where
  toInt_mul x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.SInt`,
-- as it is convenient to use the ring structure.

-- Note that we can not define `ToInt.Mod` instances for `Int8`,
-- because the condition does not hold unless `0 ≤ x.toInt ∨ y.toInt ∣ x.toInt ∨ y = 0`.

instance : ToInt.LE Int8 (.sint 8) where
  le_iff x y := by simpa using Int8.le_iff_toInt_le

instance : ToInt.LT Int8 (.sint 8) where
  lt_iff x y := by simpa using Int8.lt_iff_toInt_lt

instance : ToInt Int16 (.sint 16) where
  toInt x := x.toInt
  toInt_inj x y w := Int16.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨Int16.le_toInt x, Int16.toInt_lt x⟩

@[simp] theorem toInt_int16 (x : Int16) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Zero Int16 (.sint 16) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int16).toInt = _
    rw [Int16.toInt_zero]

instance : ToInt.OfNat Int16 (.sint 16) where
  toInt_ofNat x := by
    rw [toInt_int16, Int16.toInt_ofNat, Int16.size, Int.bmod_eq_emod, IntInterval.wrap]
    simp
    split <;> omega

instance : ToInt.Add Int16 (.sint 16) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.Mul Int16 (.sint 16) where
  toInt_mul x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.SInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.LE Int16 (.sint 16) where
  le_iff x y := by simpa using Int16.le_iff_toInt_le

instance : ToInt.LT Int16 (.sint 16) where
  lt_iff x y := by simpa using Int16.lt_iff_toInt_lt

instance : ToInt Int32 (.sint 32) where
  toInt x := x.toInt
  toInt_inj x y w := Int32.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨Int32.le_toInt x, Int32.toInt_lt x⟩

@[simp] theorem toInt_int32 (x : Int32) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Zero Int32 (.sint 32) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int32).toInt = _
    rw [Int32.toInt_zero]

instance : ToInt.OfNat Int32 (.sint 32) where
  toInt_ofNat x := by
    rw [toInt_int32, Int32.toInt_ofNat, Int32.size, Int.bmod_eq_emod, IntInterval.wrap]
    simp
    split <;> omega

instance : ToInt.Add Int32 (.sint 32) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.Mul Int32 (.sint 32) where
  toInt_mul x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.SInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.LE Int32 (.sint 32) where
  le_iff x y := by simpa using Int32.le_iff_toInt_le

instance : ToInt.LT Int32 (.sint 32) where
  lt_iff x y := by simpa using Int32.lt_iff_toInt_lt

instance : ToInt Int64 (.sint 64) where
  toInt x := x.toInt
  toInt_inj x y w := Int64.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨Int64.le_toInt x, Int64.toInt_lt x⟩

@[simp] theorem toInt_int64 (x : Int64) : ToInt.toInt x = (x.toInt : Int) := rfl

instance : ToInt.Zero Int64 (.sint 64) where
  toInt_zero := by
    -- simp -- FIXME: succeeds, but generates a `(kernel) application type mismatch` error!
    change (0 : Int64).toInt = _
    rw [Int64.toInt_zero]

instance : ToInt.OfNat Int64 (.sint 64) where
  toInt_ofNat x := by
    rw [toInt_int64, Int64.toInt_ofNat, Int64.size, Int.bmod_eq_emod, IntInterval.wrap]
    simp
    split <;> omega

instance : ToInt.Add Int64 (.sint 64) where
  toInt_add x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

instance : ToInt.Mul Int64 (.sint 64) where
  toInt_mul x y := by
    simp [Int.bmod_eq_emod]
    split <;> · simp; omega

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.SInt`,
-- as it is convenient to use the ring structure.

instance : ToInt.LE Int64 (.sint 64) where
  le_iff x y := by simpa using Int64.le_iff_toInt_le

instance : ToInt.LT Int64 (.sint 64) where
  lt_iff x y := by simpa using Int64.lt_iff_toInt_lt

instance : ToInt (BitVec v) (.uint v) where
  toInt x := (x.toNat : Int)
  toInt_inj x y w :=
    BitVec.eq_of_toNat_eq (Int.ofNat_inj.mp w)
  toInt_mem x := by simpa using Int.ofNat_lt.mpr (BitVec.isLt x)

@[simp] theorem toInt_bitVec (x : BitVec v) : ToInt.toInt x = (x.toNat : Int) := rfl

instance : ToInt.Zero (BitVec v) (.uint v) where
  toInt_zero := by simp

instance : ToInt.OfNat (BitVec v) (.uint v) where
  toInt_ofNat x := by simp

instance : ToInt.Add (BitVec v) (.uint v) where
  toInt_add x y := by simp

instance : ToInt.Mul (BitVec v) (.uint v) where
  toInt_mul x y := by simp

-- The `ToInt.Pow` instance is defined in `Init.GrindInstances.Ring.BitVec`,
-- as it is convenient to use the ring structure.

instance : ToInt.Mod (BitVec v) (.uint v) where
  toInt_mod x y := by simp

instance : ToInt.Div (BitVec v) (.uint v) where
  toInt_div x y := by simp

instance : ToInt.LE (BitVec v) (.uint v) where
  le_iff x y := by simpa using BitVec.le_def

instance : ToInt.LT (BitVec v) (.uint v) where
  lt_iff x y := by simpa using BitVec.lt_def

instance : ToInt ISize (.sint System.Platform.numBits) where
  toInt x := x.toInt
  toInt_inj x y w := ISize.toInt_inj.mp w
  toInt_mem x := by simp; exact ⟨ISize.two_pow_numBits_le_toInt x, ISize.toInt_lt_two_pow_numBits x⟩

@[simp] theorem toInt_isize (x : ISize) : ToInt.toInt x = x.toInt := rfl

instance : ToInt.Zero ISize (.sint System.Platform.numBits) where
  toInt_zero := by
    rw [toInt_isize, ISize.toInt_zero]

instance : ToInt.OfNat ISize (.sint System.Platform.numBits) where
  toInt_ofNat x := by
    rw [toInt_isize]
    simp only [ISize.toInt_ofNat, ISize.size, IntInterval.wrap, Int.sub_neg]
    rcases System.Platform.numBits_eq with h | h <;>
    · simp [h, Int.bmod_eq_emod]
      split <;> omega

instance : ToInt.Add ISize (.sint System.Platform.numBits) where
  toInt_add x y := by
    rw [toInt_isize, ISize.toInt_add, IntInterval.wrap_eq_bmod (Int.pow_nonneg (by decide))]
    have p₁ : (2 : Int) * 2 ^ (System.Platform.numBits - 1) = 2 ^ System.Platform.numBits := by
      have := System.Platform.numBits_pos
      have : System.Platform.numBits - 1 + 1 = System.Platform.numBits := by omega
      simp [← Int.pow_succ', this]
    have p₂ : ((2 : Int) ^ System.Platform.numBits).toNat = 2 ^ System.Platform.numBits := by
      rw [Int.toNat_pow_of_nonneg (by decide)]
      simp
    simp [p₁, p₂]

instance : ToInt.Mul ISize (.sint System.Platform.numBits) where
  toInt_mul x y := by
    rw [toInt_isize, ISize.toInt_mul, IntInterval.wrap_eq_bmod (Int.pow_nonneg (by decide))]
    have p₁ : (2 : Int) * 2 ^ (System.Platform.numBits - 1) = 2 ^ System.Platform.numBits := by
      have := System.Platform.numBits_pos
      have : System.Platform.numBits - 1 + 1 = System.Platform.numBits := by omega
      simp [← Int.pow_succ', this]
    have p₂ : ((2 : Int) ^ System.Platform.numBits).toNat = 2 ^ System.Platform.numBits := by
      rw [Int.toNat_pow_of_nonneg (by decide)]
      simp
    simp [p₁, p₂]

instance : ToInt.LE ISize (.sint System.Platform.numBits) where
  le_iff x y := by simpa using ISize.le_iff_toInt_le

instance : ToInt.LT ISize (.sint System.Platform.numBits) where
  lt_iff x y := by simpa using ISize.lt_iff_toInt_lt

end Lean.Grind
