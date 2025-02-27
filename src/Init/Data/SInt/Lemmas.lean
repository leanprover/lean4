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
@[simp] theorem ISize.toBitVec_ofNat (n : Nat) : (ofNat n).toBitVec = BitVec.ofNat _ n := rfl
@[simp] theorem ISize.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := rfl

@[simp] theorem Int8.neg_zero : -(0 : Int8) = 0 := rfl
@[simp] theorem Int16.neg_zero : -(0 : Int16) = 0 := rfl
@[simp] theorem Int32.neg_zero : -(0 : Int32) = 0 := rfl
@[simp] theorem Int64.neg_zero : -(0 : Int64) = 0 := rfl
@[simp] theorem ISize.neg_zero : -(0 : ISize) = 0 := ISize.toBitVec.inj (by simp)

theorem ISize.toNat_toBitVec_ofNat_of_lt {n : Nat} (h : n < 2^32) :
    (ofNat n).toBitVec.toNat = n :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (by cases USize.size_eq <;> simp_all +decide))

theorem ISize.toInt_ofInt {n : Int} (hn : -2^31 ≤ n) (hn' : n < 2^31) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self] <;> cases System.Platform.numBits_eq
    <;> (simp_all; try omega)

theorem ISize.toNatClampNeg_ofInt_eq_zero {n : Int} (hn : -2^31 ≤ n) (hn' : n ≤ 0) :
    toNatClampNeg (ofInt n) = 0 := by
  rwa [toNatClampNeg, toInt_ofInt hn (by omega), Int.toNat_eq_zero]

theorem ISize.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])

theorem ISize.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n :=
  toBitVec.inj (by simp)

theorem ISize.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]

theorem ISize.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 31) :
    toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt (by omega) (by omega), Int.toNat_ofNat]

theorem ISize.toNatClampNeg_neg_ofNat_of_le {n : Nat} (h : n ≤ 2 ^ 31) :
    toNatClampNeg (-ofNat n) = 0 := by
  rw [neg_ofNat, toNatClampNeg_ofInt_eq_zero (by omega) (by omega)]

theorem ISize.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 31) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt (by omega) (by omega)]

theorem ISize.toInt_neg_ofNat_of_le {n : Nat} (h : n ≤ 2 ^ 31) : toInt (-ofNat n) = -n := by
  rw [← ofInt_eq_ofNat, neg_ofInt, toInt_ofInt (by omega) (by omega)]
