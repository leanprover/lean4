/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.SInt.Basic
import Init.Data.BitVec.Lemmas

@[simp] theorem UInt8.toBitVec_toInt8 (x : UInt8) : x.toInt8.toBitVec = x.toBitVec := rfl
@[simp] theorem UInt16.toBitVec_toInt16 (x : UInt16) : x.toInt16.toBitVec = x.toBitVec := rfl
@[simp] theorem UInt32.toBitVec_toInt32 (x : UInt32) : x.toInt32.toBitVec = x.toBitVec := rfl
@[simp] theorem UInt64.toBitVec_toInt64 (x : UInt64) : x.toInt64.toBitVec = x.toBitVec := rfl
@[simp] theorem USize.toBitVec_toISize (x : USize) : x.toISize.toBitVec = x.toBitVec := rfl

@[simp] theorem ISize.toBitVec_neg (x : ISize) : (-x).toBitVec = -x.toBitVec := rfl
@[simp] theorem ISize.toBitVec_zero : (0 : ISize).toBitVec = 0 := rfl

@[simp] theorem Int8.neg_zero : -(0 : Int8) = 0 := rfl
@[simp] theorem Int16.neg_zero : -(0 : Int16) = 0 := rfl
@[simp] theorem Int32.neg_zero : -(0 : Int32) = 0 := rfl
@[simp] theorem Int64.neg_zero : -(0 : Int64) = 0 := rfl
@[simp] theorem ISize.neg_zero : -(0 : ISize) = 0 := ISize.toBitVec.inj (by simp)

theorem ISize.toNat_toBitVec_ofNat_of_lt {n : Nat} (h : n < 2^32) :
    (ofNat n).toBitVec.toNat = n :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (by cases USize.size_eq <;> simp_all +decide))

-- theoremISize.toInt_ofNat_of_lt {n : Nat} (h : n < 2)

theorem ISize.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 31) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, toInt, BitVec.toInt, if_pos, Int.toNat_ofNat,
    ISize.toNat_toBitVec_ofNat_of_lt (Nat.lt_trans h (by decide))]
  rw [ISize.toNat_toBitVec_ofNat_of_lt (Nat.lt_trans h (by decide))]
  cases System.Platform.numBits_eq <;> simp_all <;> omega


theorem Int.toNat_eq_zero {n : Int} : n.toNat = 0 ↔ n ≤ 0 := sorry

theorem ISize.toInt_ofInt {n : Int} (hn : -2^31 ≤ n) (hn' : n < 2^31) : toInt (ofInt n) = n := by
  rw [toInt]

theorem ISize.toNatClampNeg_ofInt_eq_zero {n : Int} (hn : -2^31 ≤ n) (hn' : n ≤ 0) : toNatClampNeg (ofInt n) = 0 := by
  rw [toNatClampNeg, toInt_ofInt hn, Int.toNat_eq_zero]
  · exact hn'
  · omega

theorem ISize.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) := by
  apply ISize.toBitVec.inj
  simp

theorem ISize.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := sorry

theorem ISize.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← ISize.neg_ofInt, ISize.ofInt_eq_ofNat]

-- theorem BitVec.toInt_pos

theorem ISize.toNatClampNeg_neg_ofNat_of_lt {n : Nat} (h₀ : 0 < n) (h : n < 2 ^ 31) : toNatClampNeg (-ofNat n) = 0 := by
  rw [toNatClampNeg, toInt, Int.toNat_eq_zero]
  apply Int.le_of_lt
  rw [BitVec.toInt_neg_iff]
  apply BitVec.msb_eq_true_iff_two_mul_ge.mp
  simp
  rw [neg_ofNat]
  apply ISize.toNatClampNeg_ofInt_eq_zero
  · omega
  · omega
  -- rw [toNatClampNeg]
  -- by_cases hn : n = 0
  -- · subst hn

  -- rw [toNatClampNeg, toInt, BitVec.toInt, if_neg, Int.toNat_eq_zero]
  -- · apply Int.sub_left_le_of_le_add
  --   simp
  --   apply Int.le_of_lt
  --   apply Int.emod_lt_of_pos
  --   cases System.Platform.numBits_eq <;> simp_all
  -- · simp only [toBitVec_neg, BitVec.toNat_neg, Nat.not_lt]
  --   rw [ISize.toNat_toBitVec_ofNat_of_lt]
  --   · cases System.Platform.numBits_eq
  --     · simp_all
  --       rw [Nat.mod_eq_of_lt]
  --       · omega
  --       ·
  --   · omega

  -- rw [toNatClampNeg, toInt, BitVec.toInt, if_pos, Int.toNat_ofNat,
  --   ISize.toNat_toBitVec_ofNat_of_lt (Nat.lt_trans h (by decide))]
  -- rw [ISize.toNat_toBitVec_ofNat_of_lt (Nat.lt_trans h (by decide))]
  -- cases System.Platform.numBits_eq <;> simp_all <;> omega
