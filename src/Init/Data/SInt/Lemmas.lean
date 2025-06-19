/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
import all Init.Data.Nat.Bitwise.Basic
import all Init.Data.SInt.Basic
import all Init.Data.BitVec.Basic
import Init.Data.BitVec.Lemmas
import Init.Data.BitVec.Bitblast
import Init.Data.Int.LemmasAux
import all Init.Data.UInt.Basic
import Init.Data.UInt.Lemmas
import Init.System.Platform

open Lean in
set_option hygiene false in
macro "declare_int_theorems" typeName:ident _bits:term:arg : command => do
  let mut cmds ← Syntax.getArgs <$> `(
  namespace $typeName

  @[int_toBitVec] theorem le_iff_toBitVec_sle {a b : $typeName} : a ≤ b ↔ a.toBitVec.sle b.toBitVec := Iff.rfl
  @[int_toBitVec] theorem lt_iff_toBitVec_slt {a b : $typeName} : a < b ↔ a.toBitVec.slt b.toBitVec := Iff.rfl

  theorem toBitVec_inj {a b : $typeName} : a.toBitVec = b.toBitVec ↔ a = b :=
    ⟨toBitVec.inj, (· ▸ rfl)⟩
  @[int_toBitVec] theorem eq_iff_toBitVec_eq {a b : $typeName} : a = b ↔ a.toBitVec = b.toBitVec :=
    toBitVec_inj.symm
  @[int_toBitVec] theorem ne_iff_toBitVec_ne {a b : $typeName} : a ≠ b ↔ a.toBitVec ≠ b.toBitVec :=
    Decidable.not_iff_not.2 eq_iff_toBitVec_eq
  @[simp] theorem toBitVec_ofNat' {n : Nat} : toBitVec (ofNat n) = BitVec.ofNat _ n := (rfl)
  @[simp, int_toBitVec] theorem toBitVec_ofNat {n : Nat} : toBitVec (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)

  @[simp, int_toBitVec] protected theorem toBitVec_add {a b : $typeName} : (a + b).toBitVec = a.toBitVec + b.toBitVec := (rfl)
  @[simp, int_toBitVec] protected theorem toBitVec_sub {a b : $typeName} : (a - b).toBitVec = a.toBitVec - b.toBitVec := (rfl)
  @[simp, int_toBitVec] protected theorem toBitVec_mul {a b : $typeName} : (a * b).toBitVec = a.toBitVec * b.toBitVec := (rfl)
  @[simp, int_toBitVec] protected theorem toBitVec_div {a b : $typeName} : (a / b).toBitVec = a.toBitVec.sdiv b.toBitVec := (rfl)
  @[simp, int_toBitVec] protected theorem toBitVec_mod {a b : $typeName} : (a % b).toBitVec = a.toBitVec.srem b.toBitVec := (rfl)

  end $typeName
  )
  return ⟨mkNullNode cmds⟩

declare_int_theorems Int8 8
declare_int_theorems Int16 16
declare_int_theorems Int32 32
declare_int_theorems Int64 64
declare_int_theorems ISize System.Platform.numBits

@[deprecated Int8.le_iff_toBitVec_sle (since := "2025-03-20")]
theorem Int8.le_def {a b : Int8} : a ≤ b ↔ a.toBitVec.sle b.toBitVec := Iff.rfl
@[deprecated Int16.le_iff_toBitVec_sle (since := "2025-03-20")]
theorem Int16.le_def {a b : Int16} : a ≤ b ↔ a.toBitVec.sle b.toBitVec := Iff.rfl
@[deprecated Int32.le_iff_toBitVec_sle (since := "2025-03-20")]
theorem Int32.le_def {a b : Int32} : a ≤ b ↔ a.toBitVec.sle b.toBitVec := Iff.rfl
@[deprecated Int64.le_iff_toBitVec_sle (since := "2025-03-20")]
theorem Int64.le_def {a b : Int64} : a ≤ b ↔ a.toBitVec.sle b.toBitVec := Iff.rfl
@[deprecated ISize.le_iff_toBitVec_sle (since := "2025-03-20")]
theorem ISize.le_def {a b : ISize} : a ≤ b ↔ a.toBitVec.sle b.toBitVec := Iff.rfl

@[deprecated Int8.lt_iff_toBitVec_slt (since := "2025-03-20")]
theorem Int8.lt_def {a b : Int8} : a < b ↔ a.toBitVec.slt b.toBitVec := Iff.rfl
@[deprecated Int16.lt_iff_toBitVec_slt (since := "2025-03-20")]
theorem Int16.lt_def {a b : Int16} : a < b ↔ a.toBitVec.slt b.toBitVec := Iff.rfl
@[deprecated Int32.lt_iff_toBitVec_slt (since := "2025-03-20")]
theorem Int32.lt_def {a b : Int32} : a < b ↔ a.toBitVec.slt b.toBitVec := Iff.rfl
@[deprecated Int64.lt_iff_toBitVec_slt (since := "2025-03-20")]
theorem Int64.lt_def {a b : Int64} : a < b ↔ a.toBitVec.slt b.toBitVec := Iff.rfl
@[deprecated ISize.lt_iff_toBitVec_slt (since := "2025-03-20")]
theorem ISize.lt_def {a b : ISize} : a < b ↔ a.toBitVec.slt b.toBitVec := Iff.rfl

theorem Int8.toInt.inj {x y : Int8} (h : x.toInt = y.toInt) : x = y := Int8.toBitVec.inj (BitVec.eq_of_toInt_eq h)
theorem Int8.toInt_inj {x y : Int8} : x.toInt = y.toInt ↔ x = y := ⟨Int8.toInt.inj, fun h => h ▸ rfl⟩
theorem Int16.toInt.inj {x y : Int16} (h : x.toInt = y.toInt) : x = y := Int16.toBitVec.inj (BitVec.eq_of_toInt_eq h)
theorem Int16.toInt_inj {x y : Int16} : x.toInt = y.toInt ↔ x = y := ⟨Int16.toInt.inj, fun h => h ▸ rfl⟩
theorem Int32.toInt.inj {x y : Int32} (h : x.toInt = y.toInt) : x = y := Int32.toBitVec.inj (BitVec.eq_of_toInt_eq h)
theorem Int32.toInt_inj {x y : Int32} : x.toInt = y.toInt ↔ x = y := ⟨Int32.toInt.inj, fun h => h ▸ rfl⟩
theorem Int64.toInt.inj {x y : Int64} (h : x.toInt = y.toInt) : x = y := Int64.toBitVec.inj (BitVec.eq_of_toInt_eq h)
theorem Int64.toInt_inj {x y : Int64} : x.toInt = y.toInt ↔ x = y := ⟨Int64.toInt.inj, fun h => h ▸ rfl⟩
theorem ISize.toInt.inj {x y : ISize} (h : x.toInt = y.toInt) : x = y := ISize.toBitVec.inj (BitVec.eq_of_toInt_eq h)
theorem ISize.toInt_inj {x y : ISize} : x.toInt = y.toInt ↔ x = y := ⟨ISize.toInt.inj, fun h => h ▸ rfl⟩

@[simp] theorem Int8.toBitVec_neg (x : Int8) : (-x).toBitVec = -x.toBitVec := (rfl)
@[simp] theorem Int16.toBitVec_neg (x : Int16) : (-x).toBitVec = -x.toBitVec := (rfl)
@[simp] theorem Int32.toBitVec_neg (x : Int32) : (-x).toBitVec = -x.toBitVec := (rfl)
@[simp] theorem Int64.toBitVec_neg (x : Int64) : (-x).toBitVec = -x.toBitVec := (rfl)
@[simp] theorem ISize.toBitVec_neg (x : ISize) : (-x).toBitVec = -x.toBitVec := (rfl)

@[simp] theorem Int8.toBitVec_zero : toBitVec 0 = 0#8 := (rfl)
@[simp] theorem Int16.toBitVec_zero : toBitVec 0 = 0#16 := (rfl)
@[simp] theorem Int32.toBitVec_zero : toBitVec 0 = 0#32 := (rfl)
@[simp] theorem Int64.toBitVec_zero : toBitVec 0 = 0#64 := (rfl)
@[simp] theorem ISize.toBitVec_zero : toBitVec 0 = 0#System.Platform.numBits := (rfl)

theorem Int8.toBitVec_one : (1 : Int8).toBitVec = 1#8 := (rfl)
theorem Int16.toBitVec_one : (1 : Int16).toBitVec = 1#16 := (rfl)
theorem Int32.toBitVec_one : (1 : Int32).toBitVec = 1#32 := (rfl)
theorem Int64.toBitVec_one : (1 : Int64).toBitVec = 1#64 := (rfl)
theorem ISize.toBitVec_one : (1 : ISize).toBitVec = 1#System.Platform.numBits := (rfl)

@[simp] theorem Int8.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)
@[simp] theorem Int16.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)
@[simp] theorem Int32.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)
@[simp] theorem Int64.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)
@[simp] theorem ISize.toBitVec_ofInt (i : Int) : (ofInt i).toBitVec = BitVec.ofInt _ i := (rfl)

@[simp] protected theorem Int8.neg_zero : -(0 : Int8) = 0 := (rfl)
@[simp] protected theorem Int16.neg_zero : -(0 : Int16) = 0 := (rfl)
@[simp] protected theorem Int32.neg_zero : -(0 : Int32) = 0 := (rfl)
@[simp] protected theorem Int64.neg_zero : -(0 : Int64) = 0 := (rfl)
@[simp] protected theorem ISize.neg_zero : -(0 : ISize) = 0 := ISize.toBitVec.inj (by simp)

theorem ISize.toNat_toBitVec_ofNat_of_lt {n : Nat} (h : n < 2^32) :
    (ofNat n).toBitVec.toNat = n :=
  Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h (by cases USize.size_eq <;> simp_all +decide))

@[simp] theorem Int8.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod Int8.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]
@[simp] theorem Int16.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod Int16.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]
@[simp] theorem Int32.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod Int32.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]
@[simp] theorem Int64.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod Int64.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]
theorem ISize.toInt_ofInt {n : Int} : toInt (ofInt n) = n.bmod ISize.size := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt]

theorem Int8.toInt_ofInt_of_le {n : Int} (hn : -2^7 ≤ n) (hn' : n < 2^7) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self (by decide) hn hn']
theorem Int16.toInt_ofInt_of_le {n : Int} (hn : -2^15 ≤ n) (hn' : n < 2^15) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self (by decide) hn hn']
theorem Int32.toInt_ofInt_of_le {n : Int} (hn : -2^31 ≤ n) (hn' : n < 2^31) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self (by decide) hn hn']
theorem Int64.toInt_ofInt_of_le {n : Int} (hn : -2^63 ≤ n) (hn' : n < 2^63) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self (by decide) hn hn']
theorem ISize.toInt_ofInt_of_le {n : Int} (hn : -2^31 ≤ n) (hn' : n < 2^31) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self] <;> cases System.Platform.numBits_eq
    <;> (simp_all; try omega)

theorem ISize.toInt_ofInt_of_two_pow_numBits_le {n : Int} (hn : -2 ^ (System.Platform.numBits - 1) ≤ n)
    (hn' : n < 2 ^ (System.Platform.numBits - 1)) : toInt (ofInt n) = n := by
  rw [toInt, toBitVec_ofInt, BitVec.toInt_ofInt_eq_self _ hn hn']
  cases System.Platform.numBits_eq <;> simp_all

theorem ISize.toNatClampNeg_ofInt_eq_zero {n : Int} (hn : -2^31 ≤ n) (hn' : n ≤ 0) :
    toNatClampNeg (ofInt n) = 0 := by
  rwa [toNatClampNeg, toInt_ofInt_of_le hn (by omega), Int.toNat_eq_zero]

theorem Int8.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])
theorem Int16.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])
theorem Int32.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])
theorem Int64.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])
theorem ISize.neg_ofInt {n : Int} : -ofInt n = ofInt (-n) :=
  toBitVec.inj (by simp [BitVec.ofInt_neg])

theorem Int8.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)
theorem Int16.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)
theorem Int32.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)
theorem Int64.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)
theorem ISize.ofInt_eq_ofNat {n : Nat} : ofInt n = ofNat n := toBitVec.inj (by simp)

@[simp] theorem Int8.toInt_ofNat {n : Nat} : toInt (ofNat n) = (n : Int).bmod Int8.size := by
  rw [← ofInt_eq_ofNat, toInt_ofInt]
@[simp] theorem Int16.toInt_ofNat {n : Nat} : toInt (ofNat n) = (n : Int).bmod Int16.size := by
  rw [← ofInt_eq_ofNat, toInt_ofInt]
@[simp] theorem Int32.toInt_ofNat {n : Nat} : toInt (ofNat n) = (n : Int).bmod Int32.size := by
  rw [← ofInt_eq_ofNat, toInt_ofInt]
@[simp] theorem Int64.toInt_ofNat {n : Nat} : toInt (ofNat n) = (n : Int).bmod Int64.size := by
  rw [← ofInt_eq_ofNat, toInt_ofInt]
@[simp] theorem ISize.toInt_ofNat {n : Nat} : toInt (ofNat n) = (n : Int).bmod ISize.size := by
  rw [← ofInt_eq_ofNat, toInt_ofInt]

theorem Int8.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]
theorem Int16.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]
theorem Int32.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]
theorem Int64.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]
theorem ISize.neg_ofNat {n : Nat} : -ofNat n = ofInt (-n) := by
  rw [← neg_ofInt, ofInt_eq_ofNat]

theorem Int8.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 7) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]
theorem Int16.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 15) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]
theorem Int32.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 31) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]
theorem Int64.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 63) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]
theorem ISize.toNatClampNeg_ofNat_of_lt {n : Nat} (h : n < 2 ^ 31) : toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega), Int.toNat_natCast]
theorem ISize.toNatClampNeg_ofNat_of_lt_two_pow_numBits {n : Nat} (h : n < 2 ^ (System.Platform.numBits - 1)) :
    toNatClampNeg (ofNat n) = n := by
  rw [toNatClampNeg, ← ofInt_eq_ofNat, toInt_ofInt_of_two_pow_numBits_le, Int.toNat_natCast]
  · cases System.Platform.numBits_eq <;> simp_all <;> omega
  · cases System.Platform.numBits_eq <;> simp_all <;> omega

theorem ISize.toNatClampNeg_neg_ofNat_of_le {n : Nat} (h : n ≤ 2 ^ 31) :
    toNatClampNeg (-ofNat n) = 0 := by
  rw [neg_ofNat, toNatClampNeg_ofInt_eq_zero (by omega) (by omega)]

theorem Int8.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 7) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]
theorem Int16.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 15) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]
theorem Int32.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 31) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]
theorem Int64.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 63) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]
theorem ISize.toInt_ofNat_of_lt {n : Nat} (h : n < 2 ^ 31) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_le (by omega) (by omega)]
theorem ISize.toInt_ofNat_of_lt_two_pow_numBits {n : Nat}
    (h : n < 2 ^ (System.Platform.numBits - 1)) : toInt (ofNat n) = n := by
  rw [← ofInt_eq_ofNat, toInt_ofInt_of_two_pow_numBits_le] <;>
    cases System.Platform.numBits_eq <;> simp_all <;> omega

theorem Int64.toInt_neg_ofNat_of_le {n : Nat} (h : n ≤ 2^63) : toInt (-ofNat n) = -n := by
  rw [← ofInt_eq_ofNat, neg_ofInt, toInt_ofInt_of_le (by omega) (by omega)]
theorem ISize.toInt_neg_ofNat_of_le {n : Nat} (h : n ≤ 2 ^ 31) : toInt (-ofNat n) = -n := by
  rw [← ofInt_eq_ofNat, neg_ofInt, toInt_ofInt_of_le (by omega) (by omega)]

theorem Int8.toInt_zero : toInt 0 = 0 := by simp
theorem Int16.toInt_zero : toInt 0 = 0 := by simp
theorem Int32.toInt_zero : toInt 0 = 0 := by simp
theorem Int64.toInt_zero : toInt 0 = 0 := by simp
theorem ISize.toInt_zero : toInt 0 = 0 := by simp

theorem Int8.toInt_minValue : Int8.minValue.toInt = -2^7 := (rfl)
theorem Int16.toInt_minValue : Int16.minValue.toInt = -2^15 := (rfl)
theorem Int32.toInt_minValue : Int32.minValue.toInt = -2^31 := (rfl)
theorem Int64.toInt_minValue : Int64.minValue.toInt = -2^63 := (rfl)
theorem ISize.toInt_minValue : ISize.minValue.toInt = -2 ^ (System.Platform.numBits - 1) := by
  rw [minValue, toInt_ofInt_of_two_pow_numBits_le] <;> cases System.Platform.numBits_eq
    <;> simp_all

theorem Int8.toInt_maxValue : Int8.maxValue.toInt = 2 ^ 7 - 1 := (rfl)
theorem Int16.toInt_maxValue : Int16.maxValue.toInt = 2 ^ 15 - 1 := (rfl)
theorem Int32.toInt_maxValue : Int32.maxValue.toInt = 2 ^ 31 - 1 := (rfl)
theorem Int64.toInt_maxValue : Int64.maxValue.toInt = 2 ^ 63 - 1 := (rfl)
theorem ISize.toInt_maxValue : ISize.maxValue.toInt = 2 ^ (System.Platform.numBits - 1) - 1:= by
  rw [maxValue, toInt_ofInt_of_two_pow_numBits_le] <;> cases System.Platform.numBits_eq
    <;> simp_all

@[simp] theorem Int8.toNatClampNeg_minValue : Int8.minValue.toNatClampNeg = 0 := (rfl)
@[simp] theorem Int16.toNatClampNeg_minValue : Int16.minValue.toNatClampNeg = 0 := (rfl)
@[simp] theorem Int32.toNatClampNeg_minValue : Int32.minValue.toNatClampNeg = 0 := (rfl)
@[simp] theorem Int64.toNatClampNeg_minValue : Int64.minValue.toNatClampNeg = 0 := (rfl)
@[simp] theorem ISize.toNatClampNeg_minValue : ISize.minValue.toNatClampNeg = 0 := by
  rw [toNatClampNeg, toInt_minValue]
  cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem UInt8.toBitVec_toInt8 (x : UInt8) : x.toInt8.toBitVec = x.toBitVec := (rfl)
@[simp] theorem UInt16.toBitVec_toInt16 (x : UInt16) : x.toInt16.toBitVec = x.toBitVec := (rfl)
@[simp] theorem UInt32.toBitVec_toInt32 (x : UInt32) : x.toInt32.toBitVec = x.toBitVec := (rfl)
@[simp] theorem UInt64.toBitVec_toInt64 (x : UInt64) : x.toInt64.toBitVec = x.toBitVec := (rfl)
@[simp] theorem USize.toBitVec_toISize (x : USize) : x.toISize.toBitVec = x.toBitVec := (rfl)

@[simp] theorem Int8.ofBitVec_uInt8ToBitVec (x : UInt8) : Int8.ofBitVec x.toBitVec = x.toInt8 := (rfl)
@[simp] theorem Int16.ofBitVec_uInt16ToBitVec (x : UInt16) : Int16.ofBitVec x.toBitVec = x.toInt16 := (rfl)
@[simp] theorem Int32.ofBitVec_uInt32ToBitVec (x : UInt32) : Int32.ofBitVec x.toBitVec = x.toInt32 := (rfl)
@[simp] theorem Int64.ofBitVec_uInt64ToBitVec (x : UInt64) : Int64.ofBitVec x.toBitVec = x.toInt64 := (rfl)
@[simp] theorem ISize.ofBitVec_uSizeToBitVec (x : USize) : ISize.ofBitVec x.toBitVec = x.toISize := (rfl)

@[simp] theorem UInt8.toUInt8_toInt8 (x : UInt8) : x.toInt8.toUInt8 = x := (rfl)
@[simp] theorem UInt16.toUInt16_toInt16 (x : UInt16) : x.toInt16.toUInt16 = x := (rfl)
@[simp] theorem UInt32.toUInt32_toInt32 (x : UInt32) : x.toInt32.toUInt32 = x := (rfl)
@[simp] theorem UInt64.toUInt64_toInt64 (x : UInt64) : x.toInt64.toUInt64 = x := (rfl)
@[simp] theorem USize.toUSize_toISize (x : USize) : x.toISize.toUSize = x := (rfl)

@[simp] theorem Int8.toNat_toInt (x : Int8) : x.toInt.toNat = x.toNatClampNeg := (rfl)
@[simp] theorem Int16.toNat_toInt (x : Int16) : x.toInt.toNat = x.toNatClampNeg := (rfl)
@[simp] theorem Int32.toNat_toInt (x : Int32) : x.toInt.toNat = x.toNatClampNeg := (rfl)
@[simp] theorem Int64.toNat_toInt (x : Int64) : x.toInt.toNat = x.toNatClampNeg := (rfl)
@[simp] theorem ISize.toNat_toInt (x : ISize) : x.toInt.toNat = x.toNatClampNeg := (rfl)

@[simp] theorem Int8.toInt_toBitVec (x : Int8) : x.toBitVec.toInt = x.toInt := (rfl)
@[simp] theorem Int16.toInt_toBitVec (x : Int16) : x.toBitVec.toInt = x.toInt := (rfl)
@[simp] theorem Int32.toInt_toBitVec (x : Int32) : x.toBitVec.toInt = x.toInt := (rfl)
@[simp] theorem Int64.toInt_toBitVec (x : Int64) : x.toBitVec.toInt = x.toInt := (rfl)
@[simp] theorem ISize.toInt_toBitVec (x : ISize) : x.toBitVec.toInt = x.toInt := (rfl)

@[simp] theorem Int8.toBitVec_toInt16 (x : Int8) : x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)
@[simp] theorem Int8.toBitVec_toInt32 (x : Int8) : x.toInt32.toBitVec = x.toBitVec.signExtend 32 := (rfl)
@[simp] theorem Int8.toBitVec_toInt64 (x : Int8) : x.toInt64.toBitVec = x.toBitVec.signExtend 64 := (rfl)
@[simp] theorem Int8.toBitVec_toISize (x : Int8) : x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)

@[simp] theorem Int16.toBitVec_toInt8 (x : Int16) : x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)
@[simp] theorem Int16.toBitVec_toInt32 (x : Int16) : x.toInt32.toBitVec = x.toBitVec.signExtend 32 := (rfl)
@[simp] theorem Int16.toBitVec_toInt64 (x : Int16) : x.toInt64.toBitVec = x.toBitVec.signExtend 64 := (rfl)
@[simp] theorem Int16.toBitVec_toISize (x : Int16) : x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)

@[simp] theorem Int32.toBitVec_toInt8 (x : Int32) : x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)
@[simp] theorem Int32.toBitVec_toInt16 (x : Int32) : x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)
@[simp] theorem Int32.toBitVec_toInt64 (x : Int32) : x.toInt64.toBitVec = x.toBitVec.signExtend 64 := (rfl)
@[simp] theorem Int32.toBitVec_toISize (x : Int32) : x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)

@[simp] theorem Int64.toBitVec_toInt8 (x : Int64) : x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)
@[simp] theorem Int64.toBitVec_toInt16 (x : Int64) : x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)
@[simp] theorem Int64.toBitVec_toInt32 (x : Int64) : x.toInt32.toBitVec = x.toBitVec.signExtend 32 := (rfl)
@[simp] theorem Int64.toBitVec_toISize (x : Int64) : x.toISize.toBitVec = x.toBitVec.signExtend System.Platform.numBits := (rfl)

@[simp] theorem ISize.toBitVec_toInt8 (x : ISize) : x.toInt8.toBitVec = x.toBitVec.signExtend 8 := (rfl)
@[simp] theorem ISize.toBitVec_toInt16 (x : ISize) : x.toInt16.toBitVec = x.toBitVec.signExtend 16 := (rfl)
@[simp] theorem ISize.toBitVec_toInt32 (x : ISize) : x.toInt32.toBitVec = x.toBitVec.signExtend 32 := (rfl)
@[simp] theorem ISize.toBitVec_toInt64 (x : ISize) : x.toInt64.toBitVec = x.toBitVec.signExtend 64 := (rfl)

theorem Int8.toInt_lt (x : Int8) : x.toInt < 2 ^ 7 := Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)
theorem Int8.le_toInt (x : Int8) : -2 ^ 7 ≤ x.toInt := Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)
theorem Int16.toInt_lt (x : Int16) : x.toInt < 2 ^ 15 := Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)
theorem Int16.le_toInt (x : Int16) : -2 ^ 15 ≤ x.toInt := Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)
theorem Int32.toInt_lt (x : Int32) : x.toInt < 2 ^ 31 := Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)
theorem Int32.le_toInt (x : Int32) : -2 ^ 31 ≤ x.toInt := Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)
theorem Int64.toInt_lt (x : Int64) : x.toInt < 2 ^ 63 := Int.lt_of_mul_lt_mul_left BitVec.two_mul_toInt_lt (by decide)
theorem Int64.le_toInt (x : Int64) : -2 ^ 63 ≤ x.toInt := Int.le_of_mul_le_mul_left BitVec.le_two_mul_toInt (by decide)
theorem ISize.toInt_lt_two_pow_numBits (x : ISize) : x.toInt < 2 ^ (System.Platform.numBits - 1) := by
  have := x.toBitVec.toInt_lt; cases System.Platform.numBits_eq <;> simp_all <;> omega
theorem ISize.two_pow_numBits_le_toInt (x : ISize) : -2 ^ (System.Platform.numBits - 1) ≤ x.toInt := by
  have := x.toBitVec.le_toInt; cases System.Platform.numBits_eq <;> simp_all <;> omega
theorem ISize.toInt_lt (x : ISize) : x.toInt < 2 ^ 63 := by
  have := x.toBitVec.toInt_lt; cases System.Platform.numBits_eq <;> simp_all <;> omega
theorem ISize.le_toInt (x : ISize) : -2 ^ 63 ≤ x.toInt := by
  have := x.toBitVec.le_toInt; cases System.Platform.numBits_eq <;> simp_all <;> omega

theorem Int8.toInt_le (x : Int8) : x.toInt ≤ Int8.maxValue.toInt := Int.le_of_lt_add_one x.toInt_lt
theorem Int16.toInt_le (x : Int16) : x.toInt ≤ Int16.maxValue.toInt := Int.le_of_lt_add_one x.toInt_lt
theorem Int32.toInt_le (x : Int32) : x.toInt ≤ Int32.maxValue.toInt := Int.le_of_lt_add_one x.toInt_lt
theorem Int64.toInt_le (x : Int64) : x.toInt ≤ Int64.maxValue.toInt := Int.le_of_lt_add_one x.toInt_lt
theorem ISize.toInt_le (x : ISize) : x.toInt ≤ ISize.maxValue.toInt := by
  rw [toInt_ofInt_of_two_pow_numBits_le]
  · exact Int.le_of_lt_add_one (by simpa using x.toInt_lt_two_pow_numBits)
  · cases System.Platform.numBits_eq <;> simp_all
  · cases System.Platform.numBits_eq <;> simp_all
theorem Int8.minValue_le_toInt (x : Int8) : Int8.minValue.toInt ≤ x.toInt := x.le_toInt
theorem Int16.minValue_le_toInt (x : Int16) : Int16.minValue.toInt ≤ x.toInt := x.le_toInt
theorem Int32.minValue_le_toInt (x : Int32) : Int32.minValue.toInt ≤ x.toInt := x.le_toInt
theorem Int64.minValue_le_toInt (x : Int64) : Int64.minValue.toInt ≤ x.toInt := x.le_toInt
theorem ISize.minValue_le_toInt (x : ISize) : ISize.minValue.toInt ≤ x.toInt := by
  rw [toInt_ofInt_of_two_pow_numBits_le]
  · exact x.two_pow_numBits_le_toInt
  · cases System.Platform.numBits_eq <;> simp_all
  · cases System.Platform.numBits_eq <;> simp_all

theorem ISize.toInt_minValue_le : ISize.minValue.toInt ≤ -2^31 := by
  rw [minValue, toInt_ofInt_of_two_pow_numBits_le] <;> cases System.Platform.numBits_eq
    <;> simp_all

theorem ISize.le_toInt_maxValue : 2 ^ 31 - 1 ≤ ISize.maxValue.toInt := by
  rw [maxValue, toInt_ofInt_of_two_pow_numBits_le] <;> cases System.Platform.numBits_eq
    <;> simp_all

theorem Int8.iSizeMinValue_le_toInt (x : Int8) : ISize.minValue.toInt ≤ x.toInt :=
  Int.le_trans (Int.le_trans ISize.toInt_minValue_le (by decide)) x.le_toInt
theorem Int8.toInt_le_iSizeMaxValue (x : Int8) : x.toInt ≤ ISize.maxValue.toInt :=
  Int.le_trans x.toInt_le (Int.le_trans (by decide) ISize.le_toInt_maxValue)
theorem Int16.iSizeMinValue_le_toInt (x : Int16) : ISize.minValue.toInt ≤ x.toInt :=
  Int.le_trans (Int.le_trans ISize.toInt_minValue_le (by decide)) x.le_toInt
theorem Int16.toInt_le_iSizeMaxValue (x : Int16) : x.toInt ≤ ISize.maxValue.toInt :=
  Int.le_trans x.toInt_le (Int.le_trans (by decide) ISize.le_toInt_maxValue)
theorem Int32.iSizeMinValue_le_toInt (x : Int32) : ISize.minValue.toInt ≤ x.toInt :=
  Int.le_trans (Int.le_trans ISize.toInt_minValue_le (by decide)) x.le_toInt
theorem Int32.toInt_le_iSizeMaxValue (x : Int32) : x.toInt ≤ ISize.maxValue.toInt :=
  Int.le_trans x.toInt_le (Int.le_trans (by decide) ISize.le_toInt_maxValue)

theorem ISize.int64MinValue_le_toInt (x : ISize) : Int64.minValue.toInt ≤ x.toInt :=
  Int.le_trans (by decide) x.le_toInt
theorem ISize.toInt_le_int64MaxValue (x : ISize) : x.toInt ≤ Int64.maxValue.toInt :=
  Int.le_of_lt_add_one x.toInt_lt

theorem Int8.toNatClampNeg_lt (x : Int8) : x.toNatClampNeg < 2 ^ 7 := (Int.toNat_lt' (by decide)).2 x.toInt_lt
theorem Int16.toNatClampNeg_lt (x : Int16) : x.toNatClampNeg < 2 ^ 15 := (Int.toNat_lt' (by decide)).2 x.toInt_lt
theorem Int32.toNatClampNeg_lt (x : Int32) : x.toNatClampNeg < 2 ^ 31 := (Int.toNat_lt' (by decide)).2 x.toInt_lt
theorem Int64.toNatClampNeg_lt (x : Int64) : x.toNatClampNeg < 2 ^ 63 := (Int.toNat_lt' (by decide)).2 x.toInt_lt
theorem ISize.toNatClampNeg_lt_two_pow_numBits (x : ISize) : x.toNatClampNeg < 2 ^ (System.Platform.numBits - 1) := by
  rw [toNatClampNeg, Int.toNat_lt', Int.natCast_pow]
  · exact x.toInt_lt_two_pow_numBits
  · cases System.Platform.numBits_eq <;> simp_all
theorem ISize.toNatClampNeg_lt (x : ISize) : x.toNatClampNeg < 2 ^ 63 := (Int.toNat_lt' (by decide)).2 x.toInt_lt

@[simp] theorem Int8.toInt_toInt16 (x : Int8) : x.toInt16.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int8.toInt_toInt32 (x : Int8) : x.toInt32.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int8.toInt_toInt64 (x : Int8) : x.toInt64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int8.toInt_toISize (x : Int8) : x.toISize.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem Int16.toInt_toInt8 (x : Int16) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem Int16.toInt_toInt32 (x : Int16) : x.toInt32.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int16.toInt_toInt64 (x : Int16) : x.toInt64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int16.toInt_toISize (x : Int16) : x.toISize.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem Int32.toInt_toInt8 (x : Int32) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem Int32.toInt_toInt16 (x : Int32) : x.toInt16.toInt = x.toInt.bmod (2 ^ 16) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem Int32.toInt_toInt64 (x : Int32) : x.toInt64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by decide)
@[simp] theorem Int32.toInt_toISize (x : Int32) : x.toISize.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem Int64.toInt_toInt8 (x : Int64) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem Int64.toInt_toInt16 (x : Int64) : x.toInt16.toInt = x.toInt.bmod (2 ^ 16) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem Int64.toInt_toInt32 (x : Int64) : x.toInt32.toInt = x.toInt.bmod (2 ^ 32) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by decide)
@[simp] theorem Int64.toInt_toISize (x : Int64) : x.toISize.toInt = x.toInt.bmod (2 ^ System.Platform.numBits) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem ISize.toInt_toInt8 (x : ISize) : x.toInt8.toInt = x.toInt.bmod (2 ^ 8) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)
@[simp] theorem ISize.toInt_toInt16 (x : ISize) : x.toInt16.toInt = x.toInt.bmod (2 ^ 16) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)
@[simp] theorem ISize.toInt_toInt32 (x : ISize) : x.toInt32.toInt = x.toInt.bmod (2 ^ 32) :=
  x.toBitVec.toInt_signExtend_eq_toInt_bmod_of_le (by cases System.Platform.numBits_eq <;> simp_all)
@[simp] theorem ISize.toInt_toInt64 (x : ISize) : x.toInt64.toInt = x.toInt :=
  x.toBitVec.toInt_signExtend_of_le (by cases System.Platform.numBits_eq <;> simp_all)

@[simp] theorem Int8.toNatClampNeg_toInt16 (x : Int8) : x.toInt16.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt16
@[simp] theorem Int8.toNatClampNeg_toInt32 (x : Int8) : x.toInt32.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt32
@[simp] theorem Int8.toNatClampNeg_toInt64 (x : Int8) : x.toInt64.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt64
@[simp] theorem Int8.toNatClampNeg_toISize (x : Int8) : x.toISize.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize

@[simp] theorem Int16.toNatClampNeg_toInt32 (x : Int16) : x.toInt32.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt32
@[simp] theorem Int16.toNatClampNeg_toInt64 (x : Int16) : x.toInt64.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt64
@[simp] theorem Int16.toNatClampNeg_toISize (x : Int16) : x.toISize.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize

@[simp] theorem Int32.toNatClampNeg_toInt64 (x : Int32) : x.toInt64.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt64
@[simp] theorem Int32.toNatClampNeg_toISize (x : Int32) : x.toISize.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toISize

@[simp] theorem ISize.toNatClampNeg_toInt64 (x : ISize) : x.toInt64.toNatClampNeg = x.toNatClampNeg :=
  congrArg Int.toNat x.toInt_toInt64

@[simp] theorem Int8.toInt8_toUInt8 (x : Int8) : x.toUInt8.toInt8 = x := (rfl)
@[simp] theorem Int16.toInt16_toUInt16 (x : Int16) : x.toUInt16.toInt16 = x := (rfl)
@[simp] theorem Int32.toInt32_toUInt32 (x : Int32) : x.toUInt32.toInt32 = x := (rfl)
@[simp] theorem Int64.toInt64_toUInt64 (x : Int64) : x.toUInt64.toInt64 = x := (rfl)
@[simp] theorem ISize.toISize_toUSize (x : ISize) : x.toUSize.toISize = x := (rfl)

theorem Int8.toNat_toBitVec (x : Int8) : x.toBitVec.toNat = x.toUInt8.toNat := (rfl)
theorem Int16.toNat_toBitVec (x : Int16) : x.toBitVec.toNat = x.toUInt16.toNat := (rfl)
theorem Int32.toNat_toBitVec (x : Int32) : x.toBitVec.toNat = x.toUInt32.toNat := (rfl)
theorem Int64.toNat_toBitVec (x : Int64) : x.toBitVec.toNat = x.toUInt64.toNat := (rfl)
theorem ISize.toNat_toBitVec (x : ISize) : x.toBitVec.toNat = x.toUSize.toNat := (rfl)

theorem Int8.toNat_toBitVec_of_le {x : Int8} (hx : 0 ≤ x) : x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm
theorem Int16.toNat_toBitVec_of_le {x : Int16} (hx : 0 ≤ x) : x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm
theorem Int32.toNat_toBitVec_of_le {x : Int32} (hx : 0 ≤ x) : x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm
theorem Int64.toNat_toBitVec_of_le {x : Int64} (hx : 0 ≤ x) : x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm
theorem ISize.toNat_toBitVec_of_le {x : ISize} (hx : 0 ≤ x) : x.toBitVec.toNat = x.toNatClampNeg :=
  (x.toBitVec.toNat_toInt_of_sle hx).symm

theorem Int8.toNat_toUInt8_of_le {x : Int8} (hx : 0 ≤ x) : x.toUInt8.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]
theorem Int16.toNat_toUInt16_of_le {x : Int16} (hx : 0 ≤ x) : x.toUInt16.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]
theorem Int32.toNat_toUInt32_of_le {x : Int32} (hx : 0 ≤ x) : x.toUInt32.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]
theorem Int64.toNat_toUInt64_of_le {x : Int64} (hx : 0 ≤ x) : x.toUInt64.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]
theorem ISize.toNat_toUSize_of_le {x : ISize} (hx : 0 ≤ x) : x.toUSize.toNat = x.toNatClampNeg := by
  rw [← toNat_toBitVec, toNat_toBitVec_of_le hx]

theorem Int8.toFin_toBitVec (x : Int8) : x.toBitVec.toFin = x.toUInt8.toFin := (rfl)
theorem Int16.toFin_toBitVec (x : Int16) : x.toBitVec.toFin = x.toUInt16.toFin := (rfl)
theorem Int32.toFin_toBitVec (x : Int32) : x.toBitVec.toFin = x.toUInt32.toFin := (rfl)
theorem Int64.toFin_toBitVec (x : Int64) : x.toBitVec.toFin = x.toUInt64.toFin := (rfl)
theorem ISize.toFin_toBitVec (x : ISize) : x.toBitVec.toFin = x.toUSize.toFin := (rfl)

@[simp] theorem Int8.toBitVec_toUInt8 (x : Int8) : x.toUInt8.toBitVec = x.toBitVec := (rfl)
@[simp] theorem Int16.toBitVec_toUInt16 (x : Int16) : x.toUInt16.toBitVec = x.toBitVec := (rfl)
@[simp] theorem Int32.toBitVec_toUInt32 (x : Int32) : x.toUInt32.toBitVec = x.toBitVec := (rfl)
@[simp] theorem Int64.toBitVec_toUInt64 (x : Int64) : x.toUInt64.toBitVec = x.toBitVec := (rfl)
@[simp] theorem ISize.toBitVec_toUSize (x : ISize) : x.toUSize.toBitVec = x.toBitVec := (rfl)

@[simp] theorem UInt8.ofBitVec_int8ToBitVec (x : Int8) : UInt8.ofBitVec x.toBitVec = x.toUInt8 := (rfl)
@[simp] theorem UInt16.ofBitVec_int16ToBitVec (x : Int16) : UInt16.ofBitVec x.toBitVec = x.toUInt16 := (rfl)
@[simp] theorem UInt32.ofBitVec_int32ToBitVec (x : Int32) : UInt32.ofBitVec x.toBitVec = x.toUInt32 := (rfl)
@[simp] theorem UInt64.ofBitVec_int64ToBitVec (x : Int64) : UInt64.ofBitVec x.toBitVec = x.toUInt64 := (rfl)
@[simp] theorem USize.ofBitVec_iSizeToBitVec (x : ISize) : USize.ofBitVec x.toBitVec = x.toUSize := (rfl)

@[simp] theorem Int8.ofBitVec_toBitVec (x : Int8) : Int8.ofBitVec x.toBitVec = x := (rfl)
@[simp] theorem Int16.ofBitVec_toBitVec (x : Int16) : Int16.ofBitVec x.toBitVec = x := (rfl)
@[simp] theorem Int32.ofBitVec_toBitVec (x : Int32) : Int32.ofBitVec x.toBitVec = x := (rfl)
@[simp] theorem Int64.ofBitVec_toBitVec (x : Int64) : Int64.ofBitVec x.toBitVec = x := (rfl)
@[simp] theorem ISize.ofBitVec_toBitVec (x : ISize) : ISize.ofBitVec x.toBitVec = x := (rfl)

@[simp] theorem Int8.ofBitVec_int16ToBitVec (x : Int16) : Int8.ofBitVec (x.toBitVec.signExtend 8) = x.toInt8 := (rfl)
@[simp] theorem Int8.ofBitVec_int32ToBitVec (x : Int32) : Int8.ofBitVec (x.toBitVec.signExtend 8) = x.toInt8 := (rfl)
@[simp] theorem Int8.ofBitVec_int64ToBitVec (x : Int64) : Int8.ofBitVec (x.toBitVec.signExtend 8) = x.toInt8 := (rfl)
@[simp] theorem Int8.ofBitVec_iSizeToBitVec (x : ISize) : Int8.ofBitVec (x.toBitVec.signExtend 8) = x.toInt8 := (rfl)

@[simp] theorem Int16.ofBitVec_int8ToBitVec (x : Int8) : Int16.ofBitVec (x.toBitVec.signExtend 16) = x.toInt16 := (rfl)
@[simp] theorem Int16.ofBitVec_int32ToBitVec (x : Int32) : Int16.ofBitVec (x.toBitVec.signExtend 16) = x.toInt16 := (rfl)
@[simp] theorem Int16.ofBitVec_int64ToBitVec (x : Int64) : Int16.ofBitVec (x.toBitVec.signExtend 16) = x.toInt16 := (rfl)
@[simp] theorem Int16.ofBitVec_iSizeToBitVec (x : ISize) : Int16.ofBitVec (x.toBitVec.signExtend 16) = x.toInt16 := (rfl)

@[simp] theorem Int32.ofBitVec_int8ToBitVec (x : Int8) : Int32.ofBitVec (x.toBitVec.signExtend 32) = x.toInt32 := (rfl)
@[simp] theorem Int32.ofBitVec_int16ToBitVec (x : Int16) : Int32.ofBitVec (x.toBitVec.signExtend 32) = x.toInt32 := (rfl)
@[simp] theorem Int32.ofBitVec_int64ToBitVec (x : Int64) : Int32.ofBitVec (x.toBitVec.signExtend 32) = x.toInt32 := (rfl)
@[simp] theorem Int32.ofBitVec_iSizeToBitVec (x : ISize) : Int32.ofBitVec (x.toBitVec.signExtend 32) = x.toInt32 := (rfl)

@[simp] theorem Int64.ofBitVec_int8ToBitVec (x : Int8) : Int64.ofBitVec (x.toBitVec.signExtend 64) = x.toInt64 := (rfl)
@[simp] theorem Int64.ofBitVec_int16ToBitVec (x : Int16) : Int64.ofBitVec (x.toBitVec.signExtend 64) = x.toInt64 := (rfl)
@[simp] theorem Int64.ofBitVec_int32ToBitVec (x : Int32) : Int64.ofBitVec (x.toBitVec.signExtend 64) = x.toInt64 := (rfl)
@[simp] theorem Int64.ofBitVec_iSizeToBitVec (x : ISize) : Int64.ofBitVec (x.toBitVec.signExtend 64) = x.toInt64 := (rfl)

@[simp] theorem ISize.ofBitVec_int8ToBitVec (x : Int8) : ISize.ofBitVec (x.toBitVec.signExtend System.Platform.numBits) = x.toISize := (rfl)
@[simp] theorem ISize.ofBitVec_int16ToBitVec (x : Int16) : ISize.ofBitVec (x.toBitVec.signExtend System.Platform.numBits) = x.toISize := (rfl)
@[simp] theorem ISize.ofBitVec_int32ToBitVec (x : Int32) : ISize.ofBitVec (x.toBitVec.signExtend System.Platform.numBits) = x.toISize := (rfl)
@[simp] theorem ISize.ofBitVec_int64ToBitVec (x : Int64) : ISize.ofBitVec (x.toBitVec.signExtend System.Platform.numBits) = x.toISize := (rfl)

@[simp] theorem Int8.toBitVec_ofIntLE (x : Int) (h₁ h₂) : (Int8.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 8 x := (rfl)
@[simp] theorem Int16.toBitVec_ofIntLE (x : Int) (h₁ h₂) : (Int16.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 16 x := (rfl)
@[simp] theorem Int32.toBitVec_ofIntLE (x : Int) (h₁ h₂) : (Int32.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 32 x := (rfl)
@[simp] theorem Int64.toBitVec_ofIntLE (x : Int) (h₁ h₂) : (Int64.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt 64 x := (rfl)
@[simp] theorem ISize.toBitVec_ofIntLE (x : Int) (h₁ h₂) : (ISize.ofIntLE x h₁ h₂).toBitVec = BitVec.ofInt System.Platform.numBits x := (rfl)

@[simp] theorem Int8.toInt_bmod (x : Int8) : x.toInt.bmod 256 = x.toInt := Int.bmod_eq_of_le x.le_toInt x.toInt_lt
@[simp] theorem Int16.toInt_bmod (x : Int16) : x.toInt.bmod 65536 = x.toInt := Int.bmod_eq_of_le x.le_toInt x.toInt_lt
@[simp] theorem Int32.toInt_bmod (x : Int32) : x.toInt.bmod 4294967296 = x.toInt := Int.bmod_eq_of_le x.le_toInt x.toInt_lt
@[simp] theorem Int64.toInt_bmod (x : Int64) : x.toInt.bmod 18446744073709551616 = x.toInt := Int.bmod_eq_of_le x.le_toInt x.toInt_lt
@[simp] theorem ISize.toInt_bmod_two_pow_numBits (x : ISize) : x.toInt.bmod (2 ^ System.Platform.numBits) = x.toInt := by
  refine Int.bmod_eq_of_le ?_ ?_
  · have := x.two_pow_numBits_le_toInt
    cases System.Platform.numBits_eq <;> simp_all
  · have := x.toInt_lt_two_pow_numBits
    cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem Int8.toInt_bmod_65536 (x : Int8) : x.toInt.bmod 65536 = x.toInt :=
  Int.bmod_eq_of_le (Int.le_trans (by decide) x.le_toInt) (Int.lt_of_lt_of_le x.toInt_lt (by decide))
@[simp] theorem Int8.toInt_bmod_4294967296 (x : Int8) : x.toInt.bmod 4294967296 = x.toInt :=
  Int.bmod_eq_of_le (Int.le_trans (by decide) x.le_toInt) (Int.lt_of_lt_of_le x.toInt_lt (by decide))
@[simp] theorem Int16.toInt_bmod_4294967296 (x : Int16) : x.toInt.bmod 4294967296 = x.toInt :=
  Int.bmod_eq_of_le (Int.le_trans (by decide) x.le_toInt) (Int.lt_of_lt_of_le x.toInt_lt (by decide))
@[simp] theorem Int8.toInt_bmod_18446744073709551616 (x : Int8) : x.toInt.bmod 18446744073709551616 = x.toInt :=
  Int.bmod_eq_of_le (Int.le_trans (by decide) x.le_toInt) (Int.lt_of_lt_of_le x.toInt_lt (by decide))
@[simp] theorem Int16.toInt_bmod_18446744073709551616 (x : Int16) : x.toInt.bmod 18446744073709551616 = x.toInt :=
  Int.bmod_eq_of_le (Int.le_trans (by decide) x.le_toInt) (Int.lt_of_lt_of_le x.toInt_lt (by decide))
@[simp] theorem Int32.toInt_bmod_18446744073709551616 (x : Int32) : x.toInt.bmod 18446744073709551616 = x.toInt :=
  Int.bmod_eq_of_le (Int.le_trans (by decide) x.le_toInt) (Int.lt_of_lt_of_le x.toInt_lt (by decide))
@[simp] theorem ISize.toInt_bmod_18446744073709551616 (x : ISize) : x.toInt.bmod 18446744073709551616 = x.toInt :=
  Int.bmod_eq_of_le x.le_toInt x.toInt_lt
@[simp] theorem Int8.toInt_bmod_two_pow_numBits (x : Int8) : x.toInt.bmod (2 ^ System.Platform.numBits) = x.toInt := by
  refine Int.bmod_eq_of_le (Int.le_trans ?_ x.iSizeMinValue_le_toInt)
    (Int.lt_of_le_sub_one (Int.le_trans x.toInt_le_iSizeMaxValue ?_))
  all_goals cases System.Platform.numBits_eq <;> simp_all [ISize.toInt_minValue, ISize.toInt_maxValue]
@[simp] theorem Int16.toInt_bmod_two_pow_numBits (x : Int16) : x.toInt.bmod (2 ^ System.Platform.numBits) = x.toInt := by
  refine Int.bmod_eq_of_le (Int.le_trans ?_ x.iSizeMinValue_le_toInt)
    (Int.lt_of_le_sub_one (Int.le_trans x.toInt_le_iSizeMaxValue ?_))
  all_goals cases System.Platform.numBits_eq <;> simp_all [ISize.toInt_minValue, ISize.toInt_maxValue]
@[simp] theorem Int32.toInt_bmod_two_pow_numBits (x : Int32) : x.toInt.bmod (2 ^ System.Platform.numBits) = x.toInt := by
  refine Int.bmod_eq_of_le (Int.le_trans ?_ x.iSizeMinValue_le_toInt)
    (Int.lt_of_le_sub_one (Int.le_trans x.toInt_le_iSizeMaxValue ?_))
  all_goals cases System.Platform.numBits_eq <;> simp_all [ISize.toInt_minValue, ISize.toInt_maxValue]

@[simp] theorem BitVec.ofInt_int8ToInt (x : Int8) : BitVec.ofInt 8 x.toInt = x.toBitVec := BitVec.eq_of_toInt_eq (by simp)
@[simp] theorem BitVec.ofInt_int16ToInt (x : Int16) : BitVec.ofInt 16 x.toInt = x.toBitVec := BitVec.eq_of_toInt_eq (by simp)
@[simp] theorem BitVec.ofInt_int32ToInt (x : Int32) : BitVec.ofInt 32 x.toInt = x.toBitVec := BitVec.eq_of_toInt_eq (by simp)
@[simp] theorem BitVec.ofInt_int64ToInt (x : Int64) : BitVec.ofInt 64 x.toInt = x.toBitVec := BitVec.eq_of_toInt_eq (by simp)
@[simp] theorem BitVec.ofInt_iSizeToInt (x : ISize) : BitVec.ofInt System.Platform.numBits x.toInt = x.toBitVec :=
  BitVec.eq_of_toInt_eq (by simp)

@[simp] theorem Int8.ofIntLE_toInt (x : Int8) : Int8.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x := Int8.toBitVec.inj (by simp)
@[simp] theorem Int16.ofIntLE_toInt (x : Int16) : Int16.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x := Int16.toBitVec.inj (by simp)
@[simp] theorem Int32.ofIntLE_toInt (x : Int32) : Int32.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x := Int32.toBitVec.inj (by simp)
@[simp] theorem Int64.ofIntLE_toInt (x : Int64) : Int64.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x := Int64.toBitVec.inj (by simp)
@[simp] theorem ISize.ofIntLE_toInt (x : ISize) : ISize.ofIntLE x.toInt x.minValue_le_toInt x.toInt_le = x := ISize.toBitVec.inj (by simp)

theorem Int8.ofIntLE_int16ToInt (x : Int16) {h₁ h₂} : Int8.ofIntLE x.toInt h₁ h₂ = x.toInt8 := (rfl)
theorem Int8.ofIntLE_int32ToInt (x : Int32) {h₁ h₂} : Int8.ofIntLE x.toInt h₁ h₂ = x.toInt8 := (rfl)
theorem Int8.ofIntLE_int64ToInt (x : Int64) {h₁ h₂} : Int8.ofIntLE x.toInt h₁ h₂ = x.toInt8 := (rfl)
theorem Int8.ofIntLE_iSizeToInt (x : ISize) {h₁ h₂} : Int8.ofIntLE x.toInt h₁ h₂ = x.toInt8 := (rfl)

@[simp] theorem Int16.ofIntLE_int8ToInt (x : Int8) :
    Int16.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt16 := (rfl)
theorem Int16.ofIntLE_int32ToInt (x : Int32) {h₁ h₂} : Int16.ofIntLE x.toInt h₁ h₂ = x.toInt16 := (rfl)
theorem Int16.ofIntLE_int64ToInt (x : Int64) {h₁ h₂} : Int16.ofIntLE x.toInt h₁ h₂ = x.toInt16 := (rfl)
theorem Int16.ofIntLE_iSizeToInt (x : ISize) {h₁ h₂} : Int16.ofIntLE x.toInt h₁ h₂ = x.toInt16 := (rfl)

@[simp] theorem Int32.ofIntLE_int8ToInt (x : Int8) :
    Int32.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt32 := (rfl)
@[simp] theorem Int32.ofIntLE_int16ToInt (x : Int16) :
    Int32.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt32 := (rfl)
theorem Int32.ofIntLE_int64ToInt (x : Int64) {h₁ h₂} : Int32.ofIntLE x.toInt h₁ h₂ = x.toInt32 := (rfl)
theorem Int32.ofIntLE_iSizeToInt (x : ISize) {h₁ h₂} : Int32.ofIntLE x.toInt h₁ h₂ = x.toInt32 := (rfl)

@[simp] theorem Int64.ofIntLE_int8ToInt (x : Int8) :
    Int64.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt64 := (rfl)
@[simp] theorem Int64.ofIntLE_int16ToInt (x : Int16) :
    Int64.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt64 := (rfl)
@[simp] theorem Int64.ofIntLE_int32ToInt (x : Int32) :
    Int64.ofIntLE x.toInt (Int.le_trans (by decide) x.minValue_le_toInt) (Int.le_trans x.toInt_le (by decide)) = x.toInt64 := (rfl)
@[simp] theorem Int64.ofIntLE_iSizeToInt (x : ISize) :
    Int64.ofIntLE x.toInt x.int64MinValue_le_toInt x.toInt_le_int64MaxValue = x.toInt64 := (rfl)

@[simp] theorem ISize.ofIntLE_int8ToInt (x : Int8) :
    ISize.ofIntLE x.toInt x.iSizeMinValue_le_toInt x.toInt_le_iSizeMaxValue = x.toISize := (rfl)
@[simp] theorem ISize.ofIntLE_int16ToInt (x : Int16) :
    ISize.ofIntLE x.toInt x.iSizeMinValue_le_toInt x.toInt_le_iSizeMaxValue = x.toISize := (rfl)
@[simp] theorem ISize.ofIntLE_int32ToInt (x : Int32) :
    ISize.ofIntLE x.toInt x.iSizeMinValue_le_toInt x.toInt_le_iSizeMaxValue = x.toISize := (rfl)
theorem ISize.ofIntLE_int64ToInt (x : Int64) {h₁ h₂} : ISize.ofIntLE x.toInt h₁ h₂ = x.toISize := (rfl)

@[simp] theorem Int8.ofInt_toInt (x : Int8) : Int8.ofInt x.toInt = x := Int8.toBitVec.inj (by simp)
@[simp] theorem Int16.ofInt_toInt (x : Int16) : Int16.ofInt x.toInt = x := Int16.toBitVec.inj (by simp)
@[simp] theorem Int32.ofInt_toInt (x : Int32) : Int32.ofInt x.toInt = x := Int32.toBitVec.inj (by simp)
@[simp] theorem Int64.ofInt_toInt (x : Int64) : Int64.ofInt x.toInt = x := Int64.toBitVec.inj (by simp)
@[simp] theorem ISize.ofInt_toInt (x : ISize) : ISize.ofInt x.toInt = x := ISize.toBitVec.inj (by simp)

@[simp] theorem Int8.ofInt_int16ToInt (x : Int16) : Int8.ofInt x.toInt = x.toInt8 := (rfl)
@[simp] theorem Int8.ofInt_int32ToInt (x : Int32) : Int8.ofInt x.toInt = x.toInt8 := (rfl)
@[simp] theorem Int8.ofInt_int64ToInt (x : Int64) : Int8.ofInt x.toInt = x.toInt8 := (rfl)
@[simp] theorem Int8.ofInt_iSizeToInt (x : ISize) : Int8.ofInt x.toInt = x.toInt8 := (rfl)

@[simp] theorem Int16.ofInt_int8ToInt (x : Int8) : Int16.ofInt x.toInt = x.toInt16 := (rfl)
@[simp] theorem Int16.ofInt_int32ToInt (x : Int32) : Int16.ofInt x.toInt = x.toInt16 := (rfl)
@[simp] theorem Int16.ofInt_int64ToInt (x : Int64) : Int16.ofInt x.toInt = x.toInt16 := (rfl)
@[simp] theorem Int16.ofInt_iSizeToInt (x : ISize) : Int16.ofInt x.toInt = x.toInt16 := (rfl)

@[simp] theorem Int32.ofInt_int8ToInt (x : Int8) : Int32.ofInt x.toInt = x.toInt32 := (rfl)
@[simp] theorem Int32.ofInt_int16ToInt (x : Int16) : Int32.ofInt x.toInt = x.toInt32 := (rfl)
@[simp] theorem Int32.ofInt_int64ToInt (x : Int64) : Int32.ofInt x.toInt = x.toInt32 := (rfl)
@[simp] theorem Int32.ofInt_iSizeToInt (x : ISize) : Int32.ofInt x.toInt = x.toInt32 := (rfl)

@[simp] theorem Int64.ofInt_int8ToInt (x : Int8) : Int64.ofInt x.toInt = x.toInt64 := (rfl)
@[simp] theorem Int64.ofInt_int16ToInt (x : Int16) : Int64.ofInt x.toInt = x.toInt64 := (rfl)
@[simp] theorem Int64.ofInt_int32ToInt (x : Int32) : Int64.ofInt x.toInt = x.toInt64 := (rfl)
@[simp] theorem Int64.ofInt_iSizeToInt (x : ISize) : Int64.ofInt x.toInt = x.toInt64 := (rfl)

@[simp] theorem ISize.ofInt_int8ToInt (x : Int8) : ISize.ofInt x.toInt = x.toISize := (rfl)
@[simp] theorem ISize.ofInt_int16ToInt (x : Int16) : ISize.ofInt x.toInt = x.toISize := (rfl)
@[simp] theorem ISize.ofInt_int32ToInt (x : Int32) : ISize.ofInt x.toInt = x.toISize := (rfl)
@[simp] theorem ISize.ofInt_int64ToInt (x : Int64) : ISize.ofInt x.toInt = x.toISize := (rfl)

@[simp] theorem Int8.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
@[simp] theorem Int16.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
@[simp] theorem Int32.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
@[simp] theorem Int64.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
@[simp] theorem ISize.toInt_ofIntLE {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂).toInt = x := by
  rw [ofIntLE, toInt_ofInt_of_two_pow_numBits_le]
  · simpa [ISize.toInt_minValue] using h₁
  · apply Int.lt_of_le_sub_one
    simpa [ISize.toInt_maxValue] using h₂

theorem Int8.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]
theorem Int16.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]
theorem Int32.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]
theorem Int64.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]
theorem ISize.ofIntLE_eq_ofIntTruncate {x : Int} {h₁ h₂} : (ofIntLE x h₁ h₂) = ofIntTruncate x := by
  rw [ofIntTruncate, dif_pos h₁, dif_pos h₂]

theorem Int8.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : Int8.ofIntLE n h₁ h₂ = Int8.ofInt n := (rfl)
theorem Int16.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : Int16.ofIntLE n h₁ h₂ = Int16.ofInt n := (rfl)
theorem Int32.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : Int32.ofIntLE n h₁ h₂ = Int32.ofInt n := (rfl)
theorem Int64.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : Int64.ofIntLE n h₁ h₂ = Int64.ofInt n := (rfl)
theorem ISize.ofIntLE_eq_ofInt {n : Int} (h₁ h₂) : ISize.ofIntLE n h₁ h₂ = ISize.ofInt n := (rfl)

theorem Int8.toInt_ofIntTruncate {x : Int} (h₁ : Int8.minValue.toInt ≤ x)
    (h₂ : x ≤ Int8.maxValue.toInt) : (Int8.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]
theorem Int16.toInt_ofIntTruncate {x : Int} (h₁ : Int16.minValue.toInt ≤ x)
    (h₂ : x ≤ Int16.maxValue.toInt) : (Int16.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]
theorem Int32.toInt_ofIntTruncate {x : Int} (h₁ : Int32.minValue.toInt ≤ x)
    (h₂ : x ≤ Int32.maxValue.toInt) : (Int32.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]
theorem Int64.toInt_ofIntTruncate {x : Int} (h₁ : Int64.minValue.toInt ≤ x)
    (h₂ : x ≤ Int64.maxValue.toInt) : (Int64.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]
theorem ISize.toInt_ofIntTruncate {x : Int} (h₁ : ISize.minValue.toInt ≤ x)
    (h₂ : x ≤ ISize.maxValue.toInt) : (ISize.ofIntTruncate x).toInt = x := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toInt_ofIntLE]

@[simp] theorem Int8.ofIntTruncate_toInt (x : Int8) : Int8.ofIntTruncate x.toInt = x :=
  Int8.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)
@[simp] theorem Int16.ofIntTruncate_toInt (x : Int16) : Int16.ofIntTruncate x.toInt = x :=
  Int16.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)
@[simp] theorem Int32.ofIntTruncate_toInt (x : Int32) : Int32.ofIntTruncate x.toInt = x :=
  Int32.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)
@[simp] theorem Int64.ofIntTruncate_toInt (x : Int64) : Int64.ofIntTruncate x.toInt = x :=
  Int64.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)
@[simp] theorem ISize.ofIntTruncate_toInt (x : ISize) : ISize.ofIntTruncate x.toInt = x :=
  ISize.toInt.inj (toInt_ofIntTruncate x.minValue_le_toInt x.toInt_le)

@[simp] theorem Int16.ofIntTruncate_int8ToInt (x : Int8) : Int16.ofIntTruncate x.toInt = x.toInt16 :=
  Int16.toInt.inj (by
    rw [toInt_ofIntTruncate, Int8.toInt_toInt16]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
@[simp] theorem Int32.ofIntTruncate_int8ToInt (x : Int8) : Int32.ofIntTruncate x.toInt = x.toInt32 :=
  Int32.toInt.inj (by
    rw [toInt_ofIntTruncate, Int8.toInt_toInt32]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
@[simp] theorem Int64.ofIntTruncate_int8ToInt (x : Int8) : Int64.ofIntTruncate x.toInt = x.toInt64 :=
  Int64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int8.toInt_toInt64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
@[simp] theorem ISize.ofIntTruncate_int8ToInt (x : Int8) : ISize.ofIntTruncate x.toInt = x.toISize :=
  ISize.toInt.inj (by
    rw [toInt_ofIntTruncate, Int8.toInt_toISize]
    · exact x.iSizeMinValue_le_toInt
    · exact x.toInt_le_iSizeMaxValue)

@[simp] theorem Int32.ofIntTruncate_int16ToInt (x : Int16) : Int32.ofIntTruncate x.toInt = x.toInt32 :=
  Int32.toInt.inj (by
    rw [toInt_ofIntTruncate, Int16.toInt_toInt32]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
@[simp] theorem Int64.ofIntTruncate_int16ToInt (x : Int16) : Int64.ofIntTruncate x.toInt = x.toInt64 :=
  Int64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int16.toInt_toInt64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
@[simp] theorem ISize.ofIntTruncate_int16ToInt (x : Int16) : ISize.ofIntTruncate x.toInt = x.toISize :=
  ISize.toInt.inj (by
    rw [toInt_ofIntTruncate, Int16.toInt_toISize]
    · exact x.iSizeMinValue_le_toInt
    · exact x.toInt_le_iSizeMaxValue)

@[simp] theorem Int64.ofIntTruncate_int32ToInt (x : Int32) : Int64.ofIntTruncate x.toInt = x.toInt64 :=
  Int64.toInt.inj (by
    rw [toInt_ofIntTruncate, Int32.toInt_toInt64]
    · exact Int.le_trans (by decide) x.minValue_le_toInt
    · exact Int.le_trans x.toInt_le (by decide))
@[simp] theorem ISize.ofIntTruncate_int32ToInt (x : Int32) : ISize.ofIntTruncate x.toInt = x.toISize :=
  ISize.toInt.inj (by
    rw [toInt_ofIntTruncate, Int32.toInt_toISize]
    · exact x.iSizeMinValue_le_toInt
    · exact x.toInt_le_iSizeMaxValue)

@[simp] theorem Int64.ofIntTruncate_iSizeToInt (x : ISize) : Int64.ofIntTruncate x.toInt = x.toInt64 :=
  Int64.toInt.inj (by
    rw [toInt_ofIntTruncate, ISize.toInt_toInt64]
    · exact x.int64MinValue_le_toInt
    · exact x.toInt_le_int64MaxValue)

theorem Int8.le_iff_toInt_le {x y : Int8} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le
theorem Int16.le_iff_toInt_le {x y : Int16} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le
theorem Int32.le_iff_toInt_le {x y : Int32} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le
theorem Int64.le_iff_toInt_le {x y : Int64} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le
theorem ISize.le_iff_toInt_le {x y : ISize} : x ≤ y ↔ x.toInt ≤ y.toInt := BitVec.sle_iff_toInt_le

theorem Int8.lt_iff_toInt_lt {x y : Int8} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt
theorem Int16.lt_iff_toInt_lt {x y : Int16} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt
theorem Int32.lt_iff_toInt_lt {x y : Int32} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt
theorem Int64.lt_iff_toInt_lt {x y : Int64} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt
theorem ISize.lt_iff_toInt_lt {x y : ISize} : x < y ↔ x.toInt < y.toInt := BitVec.slt_iff_toInt_lt

theorem Int8.cast_toNatClampNeg (x : Int8) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]
theorem Int16.cast_toNatClampNeg (x : Int16) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]
theorem Int32.cast_toNatClampNeg (x : Int32) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]
theorem Int64.cast_toNatClampNeg (x : Int64) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]
theorem ISize.cast_toNatClampNeg (x : ISize) (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt := by
  rw [toNatClampNeg, toInt, Int.toNat_of_nonneg (by simpa using le_iff_toInt_le.1 hx)]

theorem Int8.ofNat_toNatClampNeg (x : Int8) (hx : 0 ≤ x) : Int8.ofNat x.toNatClampNeg = x :=
  Int8.toInt.inj (by rw [Int8.toInt_ofNat_of_lt x.toNatClampNeg_lt, cast_toNatClampNeg _ hx])
theorem Int16.ofNat_toNatClampNeg (x : Int16) (hx : 0 ≤ x) : Int16.ofNat x.toNatClampNeg = x :=
  Int16.toInt.inj (by rw [Int16.toInt_ofNat_of_lt x.toNatClampNeg_lt, cast_toNatClampNeg _ hx])
theorem Int32.ofNat_toNatClampNeg (x : Int32) (hx : 0 ≤ x) : Int32.ofNat x.toNatClampNeg = x :=
  Int32.toInt.inj (by rw [Int32.toInt_ofNat_of_lt x.toNatClampNeg_lt, cast_toNatClampNeg _ hx])
theorem Int64.ofNat_toNatClampNeg (x : Int64) (hx : 0 ≤ x) : Int64.ofNat x.toNatClampNeg = x :=
  Int64.toInt.inj (by rw [Int64.toInt_ofNat_of_lt x.toNatClampNeg_lt, cast_toNatClampNeg _ hx])
theorem ISize.ofNat_toNatClampNeg (x : ISize) (hx : 0 ≤ x) : ISize.ofNat x.toNatClampNeg = x :=
  ISize.toInt.inj (by rw [ISize.toInt_ofNat_of_lt_two_pow_numBits x.toNatClampNeg_lt_two_pow_numBits,
    cast_toNatClampNeg _ hx])

theorem Int16.ofNat_int8ToNatClampNeg (x : Int8) (hx : 0 ≤ x) : Int16.ofNat x.toNatClampNeg = x.toInt16 :=
  Int16.toInt.inj (by rw [Int16.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int8.cast_toNatClampNeg _ hx, Int8.toInt_toInt16])
theorem Int32.ofNat_int8ToNatClampNeg (x : Int8) (hx : 0 ≤ x) : Int32.ofNat x.toNatClampNeg = x.toInt32 :=
  Int32.toInt.inj (by rw [Int32.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int8.cast_toNatClampNeg _ hx, Int8.toInt_toInt32])
theorem Int64.ofNat_int8ToNatClampNeg (x : Int8) (hx : 0 ≤ x) : Int64.ofNat x.toNatClampNeg = x.toInt64 :=
  Int64.toInt.inj (by rw [Int64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int8.cast_toNatClampNeg _ hx, Int8.toInt_toInt64])
theorem ISize.ofNat_int8ToNatClampNeg (x : Int8) (hx : 0 ≤ x) : ISize.ofNat x.toNatClampNeg = x.toISize :=
  ISize.toInt.inj (by rw [ISize.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int8.cast_toNatClampNeg _ hx, Int8.toInt_toISize])

theorem Int32.ofNat_int16ToNatClampNeg (x : Int16) (hx : 0 ≤ x) : Int32.ofNat x.toNatClampNeg = x.toInt32 :=
  Int32.toInt.inj (by rw [Int32.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int16.cast_toNatClampNeg _ hx, Int16.toInt_toInt32])
theorem Int64.ofNat_int16ToNatClampNeg (x : Int16) (hx : 0 ≤ x) : Int64.ofNat x.toNatClampNeg = x.toInt64 :=
  Int64.toInt.inj (by rw [Int64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int16.cast_toNatClampNeg _ hx, Int16.toInt_toInt64])
theorem ISize.ofNat_int16ToNatClampNeg (x : Int16) (hx : 0 ≤ x) : ISize.ofNat x.toNatClampNeg = x.toISize :=
  ISize.toInt.inj (by rw [ISize.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int16.cast_toNatClampNeg _ hx, Int16.toInt_toISize])

theorem Int64.ofNat_int32ToNatClampNeg (x : Int32) (hx : 0 ≤ x) : Int64.ofNat x.toNatClampNeg = x.toInt64 :=
  Int64.toInt.inj (by rw [Int64.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int32.cast_toNatClampNeg _ hx, Int32.toInt_toInt64])
theorem ISize.ofNat_int32ToNatClampNeg (x : Int32) (hx : 0 ≤ x) : ISize.ofNat x.toNatClampNeg = x.toISize :=
  ISize.toInt.inj (by rw [ISize.toInt_ofNat_of_lt (Nat.lt_of_lt_of_le x.toNatClampNeg_lt (by decide)),
    Int32.cast_toNatClampNeg _ hx, Int32.toInt_toISize])

@[simp] theorem Int8.toInt8_toInt16 (n : Int8) : n.toInt16.toInt8 = n :=
  Int8.toInt.inj (by simp)
@[simp] theorem Int8.toInt8_toInt32 (n : Int8) : n.toInt32.toInt8 = n :=
  Int8.toInt.inj (by simp)
@[simp] theorem Int8.toInt8_toInt64 (n : Int8) : n.toInt64.toInt8 = n :=
  Int8.toInt.inj (by simp)
@[simp] theorem Int8.toInt8_toISize (n : Int8) : n.toISize.toInt8 = n :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int8.toInt16_toInt32 (n : Int8) : n.toInt32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)
@[simp] theorem Int8.toInt16_toInt64 (n : Int8) : n.toInt64.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)
@[simp] theorem Int8.toInt16_toISize (n : Int8) : n.toISize.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int8.toInt32_toInt16 (n : Int8) : n.toInt16.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)
@[simp] theorem Int8.toInt32_toInt64 (n : Int8) : n.toInt64.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)
@[simp] theorem Int8.toInt32_toISize (n : Int8) : n.toISize.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int8.toInt64_toInt16 (n : Int8) : n.toInt16.toInt64 = n.toInt64 :=
  Int64.toInt.inj (by simp)
@[simp] theorem Int8.toInt64_toInt32 (n : Int8) : n.toInt32.toInt64 = n.toInt64 :=
  Int64.toInt.inj (by simp)
@[simp] theorem Int8.toInt64_toISize (n : Int8) : n.toISize.toInt64 = n.toInt64 :=
  Int64.toInt.inj (by simp)

@[simp] theorem Int8.toISize_toInt16 (n : Int8) : n.toInt16.toISize = n.toISize :=
  ISize.toInt.inj (by simp)
@[simp] theorem Int8.toISize_toInt32 (n : Int8) : n.toInt32.toISize = n.toISize :=
  ISize.toInt.inj (by simp)
@[simp] theorem Int8.toISize_toInt64 (n : Int8) : n.toInt64.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int16.toInt8_toInt32 (n : Int16) : n.toInt32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)
@[simp] theorem Int16.toInt8_toInt64 (n : Int16) : n.toInt64.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)
@[simp] theorem Int16.toInt8_toISize (n : Int16) : n.toISize.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int16.toInt16_toInt32 (n : Int16) : n.toInt32.toInt16 = n :=
  Int16.toInt.inj (by simp)
@[simp] theorem Int16.toInt16_toInt64 (n : Int16) : n.toInt64.toInt16 = n :=
  Int16.toInt.inj (by simp)
@[simp] theorem Int16.toInt16_toISize (n : Int16) : n.toISize.toInt16 = n :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int16.toInt32_toInt64 (n : Int16) : n.toInt64.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)
@[simp] theorem Int16.toInt32_toISize (n : Int16) : n.toISize.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int16.toInt64_toInt32 (n : Int16) : n.toInt32.toInt64 = n.toInt64 :=
  Int64.toInt.inj (by simp)
@[simp] theorem Int16.toInt64_toISize (n : Int16) : n.toISize.toInt64 = n.toInt64 :=
  Int64.toInt.inj (by simp)

@[simp] theorem Int16.toISize_toInt32 (n : Int16) : n.toInt32.toISize = n.toISize :=
  ISize.toInt.inj (by simp)
@[simp] theorem Int16.toISize_toInt64 (n : Int16) : n.toInt64.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int32.toInt8_toInt16 (n : Int32) : n.toInt16.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int32.toInt8_toInt64 (n : Int32) : n.toInt64.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)
@[simp] theorem Int32.toInt8_toISize (n : Int32) : n.toISize.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem Int32.toInt16_toInt64 (n : Int32) : n.toInt64.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)
@[simp] theorem Int32.toInt16_toISize (n : Int32) : n.toISize.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem Int32.toInt32_toInt64 (n : Int32) : n.toInt64.toInt32 = n :=
  Int32.toInt.inj (by simp)
@[simp] theorem Int32.toInt32_toISize (n : Int32) : n.toISize.toInt32 = n :=
  Int32.toInt.inj (by simp)

@[simp] theorem Int32.toInt64_toISize (n : Int32) : n.toISize.toInt64 = n.toInt64 :=
  Int64.toInt.inj (by simp)

@[simp] theorem Int32.toISize_toInt64 (n : Int32) : n.toInt64.toISize = n.toISize :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int64.toInt8_toInt16 (n : Int64) : n.toInt16.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int64.toInt8_toInt32 (n : Int64) : n.toInt32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int64.toInt8_toISize (n : Int64) : n.toISize.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem Int64.toInt16_toInt32 (n : Int64) : n.toInt32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int64.toInt16_toISize (n : Int64) : n.toISize.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem Int64.toInt32_toISize (n : Int64) : n.toISize.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by cases System.Platform.numBits_eq <;> simp_all))

@[simp] theorem ISize.toInt8_toInt16 (n : ISize) : n.toInt16.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize.toInt8_toInt32 (n : ISize) : n.toInt32.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize.toInt8_toInt64 (n : ISize) : n.toInt64.toInt8 = n.toInt8 :=
  Int8.toInt.inj (by simp)

@[simp] theorem ISize.toInt16_toInt32 (n : ISize) : n.toInt32.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize.toInt16_toInt64 (n : ISize) : n.toInt64.toInt16 = n.toInt16 :=
  Int16.toInt.inj (by simp)

@[simp] theorem ISize.toInt32_toInt64 (n : ISize) : n.toInt64.toInt32 = n.toInt32 :=
  Int32.toInt.inj (by simp)

@[simp] theorem ISize.toISize_toInt64 (n : ISize) : n.toInt64.toISize = n :=
  ISize.toInt.inj (by simp)

theorem UInt8.toInt8_ofNatLT {n : Nat} (hn) : (UInt8.ofNatLT n hn).toInt8 = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])
theorem UInt16.toInt16_ofNatLT {n : Nat} (hn) : (UInt16.ofNatLT n hn).toInt16 = Int16.ofNat n :=
  Int16.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])
theorem UInt32.toInt32_ofNatLT {n : Nat} (hn) : (UInt32.ofNatLT n hn).toInt32 = Int32.ofNat n :=
  Int32.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])
theorem UInt64.toInt64_ofNatLT {n : Nat} (hn) : (UInt64.ofNatLT n hn).toInt64 = Int64.ofNat n :=
  Int64.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])
theorem USize.toISize_ofNatLT {n : Nat} (hn) : (USize.ofNatLT n hn).toISize = ISize.ofNat n :=
  ISize.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat])

@[simp] theorem UInt8.toInt8_ofNat' {n : Nat} : (UInt8.ofNat n).toInt8 = Int8.ofNat n := (rfl)
@[simp] theorem UInt16.toInt16_ofNat' {n : Nat} : (UInt16.ofNat n).toInt16 = Int16.ofNat n := (rfl)
@[simp] theorem UInt32.toInt32_ofNat' {n : Nat} : (UInt32.ofNat n).toInt32 = Int32.ofNat n := (rfl)
@[simp] theorem UInt64.toInt64_ofNat' {n : Nat} : (UInt64.ofNat n).toInt64 = Int64.ofNat n := (rfl)
@[simp] theorem USize.toISize_ofNat' {n : Nat} : (USize.ofNat n).toISize = ISize.ofNat n := (rfl)

@[simp] theorem UInt8.toInt8_ofNat {n : Nat} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)
@[simp] theorem UInt16.toInt16_ofNat {n : Nat} : toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)
@[simp] theorem UInt32.toInt32_ofNat {n : Nat} : toInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)
@[simp] theorem UInt64.toInt64_ofNat {n : Nat} : toInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)
@[simp] theorem USize.toISize_ofNat {n : Nat} : toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := (rfl)

@[simp] theorem UInt8.toInt8_ofBitVec (b) : (UInt8.ofBitVec b).toInt8 = Int8.ofBitVec b := (rfl)
@[simp] theorem UInt16.toInt16_ofBitVec (b) : (UInt16.ofBitVec b).toInt16 = Int16.ofBitVec b := (rfl)
@[simp] theorem UInt32.toInt32_ofBitVec (b) : (UInt32.ofBitVec b).toInt32 = Int32.ofBitVec b := (rfl)
@[simp] theorem UInt64.toInt64_ofBitVec (b) : (UInt64.ofBitVec b).toInt64 = Int64.ofBitVec b := (rfl)
@[simp] theorem USize.toISize_ofBitVec (b) : (USize.ofBitVec b).toISize = ISize.ofBitVec b := (rfl)

@[simp] theorem Int8.toBitVec_ofBitVec (b) : (Int8.ofBitVec b).toBitVec = b := (rfl)
@[simp] theorem Int16.toBitVec_ofBitVec (b) : (Int16.ofBitVec b).toBitVec = b := (rfl)
@[simp] theorem Int32.toBitVec_ofBitVec (b) : (Int32.ofBitVec b).toBitVec = b := (rfl)
@[simp] theorem Int64.toBitVec_ofBitVec (b) : (Int64.ofBitVec b).toBitVec = b := (rfl)
@[simp] theorem ISize.toBitVec_ofBitVec (b) : (ISize.ofBitVec b).toBitVec = b := (rfl)

theorem Int8.toBitVec_ofIntTruncate {n : Int} (h₁ : Int8.minValue.toInt ≤ n) (h₂ : n ≤ Int8.maxValue.toInt) :
    (Int8.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]
theorem Int16.toBitVec_ofIntTruncate {n : Int} (h₁ : Int16.minValue.toInt ≤ n) (h₂ : n ≤ Int16.maxValue.toInt) :
    (Int16.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]
theorem Int32.toBitVec_ofIntTruncate {n : Int} (h₁ : Int32.minValue.toInt ≤ n) (h₂ : n ≤ Int32.maxValue.toInt) :
    (Int32.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]
theorem Int64.toBitVec_ofIntTruncate {n : Int} (h₁ : Int64.minValue.toInt ≤ n) (h₂ : n ≤ Int64.maxValue.toInt) :
    (Int64.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]
theorem ISize.toBitVec_ofIntTruncate {n : Int} (h₁ : ISize.minValue.toInt ≤ n) (h₂ : n ≤ ISize.maxValue.toInt) :
    (ISize.ofIntTruncate n).toBitVec = BitVec.ofInt _ n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := h₂), toBitVec_ofIntLE]

@[simp] theorem Int8.toInt_ofBitVec (b) : (Int8.ofBitVec b).toInt = b.toInt := (rfl)
@[simp] theorem Int16.toInt_ofBitVec (b) : (Int16.ofBitVec b).toInt = b.toInt := (rfl)
@[simp] theorem Int32.toInt_ofBitVec (b) : (Int32.ofBitVec b).toInt = b.toInt := (rfl)
@[simp] theorem Int64.toInt_ofBitVec (b) : (Int64.ofBitVec b).toInt = b.toInt := (rfl)
@[simp] theorem ISize.toInt_ofBitVec (b) : (ISize.ofBitVec b).toInt = b.toInt := (rfl)

@[simp] theorem Int8.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) : (Int8.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
@[simp] theorem Int16.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) : (Int16.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
@[simp] theorem Int32.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) : (Int32.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
@[simp] theorem Int64.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) : (Int64.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_le h₁ (Int.lt_of_le_sub_one h₂)]
@[simp] theorem ISize.toNatClampNeg_ofIntLE {n : Int} (h₁ h₂) : (ISize.ofIntLE n h₁ h₂).toNatClampNeg = n.toNat := by
  rw [ofIntLE, toNatClampNeg, toInt_ofInt_of_two_pow_numBits_le]
  · rwa [← ISize.toInt_minValue]
  · apply Int.lt_of_le_sub_one
    rwa [← ISize.toInt_maxValue]

@[simp] theorem Int8.toNatClampNeg_ofBitVec (b) : (Int8.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)
@[simp] theorem Int16.toNatClampNeg_ofBitVec (b) : (Int16.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)
@[simp] theorem Int32.toNatClampNeg_ofBitVec (b) : (Int32.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)
@[simp] theorem Int64.toNatClampNeg_ofBitVec (b) : (Int64.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)
@[simp] theorem ISize.toNatClampNeg_ofBitVec (b) : (ISize.ofBitVec b).toNatClampNeg = b.toInt.toNat := (rfl)

theorem Int8.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 7 ≤ n) (h₂ : n < 2 ^ 7) :
    (Int8.ofInt n).toNatClampNeg = n.toNat := by rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]
theorem Int16.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 15 ≤ n) (h₂ : n < 2 ^ 15) :
    (Int16.ofInt n).toNatClampNeg = n.toNat := by rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]
theorem Int32.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 31 ≤ n) (h₂ : n < 2 ^ 31) :
    (Int32.ofInt n).toNatClampNeg = n.toNat := by rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]
theorem Int64.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (Int64.ofInt n).toNatClampNeg = n.toNat := by rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]
theorem ISize.toNatClampNeg_ofInt_of_le {n : Int} (h₁ : -2 ^ 31 ≤ n)
    (h₂ : n < 2 ^ 31) : (ISize.ofInt n).toNatClampNeg = n.toNat := by
  rw [toNatClampNeg, toInt_ofInt_of_le h₁ h₂]
theorem ISize.toNatClampNeg_ofInt_of_two_pow_numBits {n : Int} (h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n)
    (h₂ : n < 2 ^ (System.Platform.numBits - 1)) : (ISize.ofInt n).toNatClampNeg = n.toNat := by
  rw [toNatClampNeg, toInt_ofInt_of_two_pow_numBits_le h₁ h₂]

theorem Int8.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 7) :
    (Int8.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  · next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega
theorem Int16.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 15) :
    (Int16.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  · next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega
theorem Int32.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 31) :
    (Int32.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  · next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega
theorem Int64.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 63) :
    (Int64.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  · next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega
theorem ISize.toNatClampNeg_ofIntTruncate_of_lt_two_pow_numBits {n : Int} (h₁ : n < 2 ^ (System.Platform.numBits - 1)) :
    (ISize.ofIntTruncate n).toNatClampNeg = n.toNat := by
  rw [ofIntTruncate]
  split
  · rw [dif_pos (by rw [toInt_maxValue]; omega), toNatClampNeg_ofIntLE]
  · next h =>
    rw [toNatClampNeg_minValue, eq_comm, Int.toNat_eq_zero]
    rw [toInt_minValue] at h
    omega
theorem ISize.toNatClampNeg_ofIntTruncate_of_lt {n : Int} (h₁ : n < 2 ^ 31) :
    (ISize.ofIntTruncate n).toNatClampNeg = n.toNat := by
  apply ISize.toNatClampNeg_ofIntTruncate_of_lt_two_pow_numBits (Int.lt_of_lt_of_le h₁ _)
  cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem Int8.toUInt8_ofBitVec (b) : (Int8.ofBitVec b).toUInt8 = UInt8.ofBitVec b := (rfl)
@[simp] theorem Int16.toUInt16_ofBitVec (b) : (Int16.ofBitVec b).toUInt16 = UInt16.ofBitVec b := (rfl)
@[simp] theorem Int32.toUInt32_ofBitVec (b) : (Int32.ofBitVec b).toUInt32 = UInt32.ofBitVec b := (rfl)
@[simp] theorem Int64.toUInt64_ofBitVec (b) : (Int64.ofBitVec b).toUInt64 = UInt64.ofBitVec b := (rfl)
@[simp] theorem ISize.toUSize_ofBitVec (b) : (ISize.ofBitVec b).toUSize = USize.ofBitVec b := (rfl)

@[simp] theorem Int8.toUInt8_ofNat' {n} : (Int8.ofNat n).toUInt8 = UInt8.ofNat n := (rfl)
@[simp] theorem Int16.toUInt16_ofNat' {n} : (Int16.ofNat n).toUInt16 = UInt16.ofNat n := (rfl)
@[simp] theorem Int32.toUInt32_ofNat' {n} : (Int32.ofNat n).toUInt32 = UInt32.ofNat n := (rfl)
@[simp] theorem Int64.toUInt64_ofNat' {n} : (Int64.ofNat n).toUInt64 = UInt64.ofNat n := (rfl)
@[simp] theorem ISize.toUSize_ofNat' {n} : (ISize.ofNat n).toUSize = USize.ofNat n := (rfl)

@[simp] theorem Int8.toUInt8_ofNat {n} : toUInt8 (OfNat.ofNat n) = OfNat.ofNat n := (rfl)
@[simp] theorem Int16.toUInt16_ofNat {n} : toUInt16 (OfNat.ofNat n) = OfNat.ofNat n := (rfl)
@[simp] theorem Int32.toUInt32_ofNat {n} : toUInt32 (OfNat.ofNat n) = OfNat.ofNat n := (rfl)
@[simp] theorem Int64.toUInt64_ofNat {n} : toUInt64 (OfNat.ofNat n) = OfNat.ofNat n := (rfl)
@[simp] theorem ISize.toUSize_ofNat {n} : toUSize (OfNat.ofNat n) = OfNat.ofNat n := (rfl)

theorem Int16.toInt8_ofIntLE {n} (h₁ h₂) : (Int16.ofIntLE n h₁ h₂).toInt8 = Int8.ofInt n := Int8.toInt.inj (by simp)
theorem Int32.toInt8_ofIntLE {n} (h₁ h₂) : (Int32.ofIntLE n h₁ h₂).toInt8 = Int8.ofInt n := Int8.toInt.inj (by simp)
theorem Int64.toInt8_ofIntLE {n} (h₁ h₂) : (Int64.ofIntLE n h₁ h₂).toInt8 = Int8.ofInt n := Int8.toInt.inj (by simp)
theorem ISize.toInt8_ofIntLE {n} (h₁ h₂) : (ISize.ofIntLE n h₁ h₂).toInt8 = Int8.ofInt n := Int8.toInt.inj (by simp)

@[simp] theorem Int16.toInt8_ofBitVec (b) : (Int16.ofBitVec b).toInt8 = Int8.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int32.toInt8_ofBitVec (b) : (Int32.ofBitVec b).toInt8 = Int8.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int64.toInt8_ofBitVec (b) : (Int64.ofBitVec b).toInt8 = Int8.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem ISize.toInt8_ofBitVec (b) : (ISize.ofBitVec b).toInt8 = Int8.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int16.toInt8_ofNat' {n} : (Int16.ofNat n).toInt8 = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem Int32.toInt8_ofNat' {n} : (Int32.ofNat n).toInt8 = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem Int64.toInt8_ofNat' {n} : (Int64.ofNat n).toInt8 = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem ISize.toInt8_ofNat' {n} : (ISize.ofNat n).toInt8 = Int8.ofNat n := by
  apply Int8.toBitVec.inj
  simp only [toBitVec_toInt8, toBitVec_ofNat', Int8.toBitVec_ofNat']
  rw [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_ofNat_of_le]
  all_goals cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem Int16.toInt8_ofInt {n} : (Int16.ofInt n).toInt8 = Int8.ofInt n :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int32.toInt8_ofInt {n} : (Int32.ofInt n).toInt8 = Int8.ofInt n :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int64.toInt8_ofInt {n} : (Int64.ofInt n).toInt8 = Int8.ofInt n :=
  Int8.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize.toInt8_ofInt {n} : (ISize.ofInt n).toInt8 = Int8.ofInt n := by
  apply Int8.toInt.inj
  simp only [toInt_toInt8, toInt_ofInt, Nat.reducePow, Int8.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd UInt8.size_dvd_usizeSize

@[simp] theorem Int16.toInt8_ofNat {n} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt8_ofNat'
@[simp] theorem Int32.toInt8_ofNat {n} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt8_ofNat'
@[simp] theorem Int64.toInt8_ofNat {n} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt8_ofNat'
@[simp] theorem ISize.toInt8_ofNat {n} : toInt8 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt8_ofNat'

theorem Int16.toInt8_ofIntTruncate {n : Int} (h₁ : -2 ^ 15 ≤ n) (h₂ : n < 2 ^ 15) :
    (Int16.ofIntTruncate n).toInt8 = Int8.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt8_ofIntLE]
theorem Int32.toInt8_ofIntTruncate {n : Int} (h₁ : -2 ^ 31 ≤ n) (h₂ : n < 2 ^ 31) :
    (Int32.ofIntTruncate n).toInt8 = Int8.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt8_ofIntLE]
theorem Int64.toInt8_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (Int64.ofIntTruncate n).toInt8 = Int8.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt8_ofIntLE]
theorem ISize.toInt8_ofIntTruncate {n : Int} (h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n)
    (h₂ : n < 2 ^ (System.Platform.numBits - 1)) : (ISize.ofIntTruncate n).toInt8 = Int8.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate, toInt8_ofIntLE]
  · exact toInt_minValue ▸ h₁
  · rw [toInt_maxValue]
    omega

theorem Int32.toInt16_ofIntLE {n} (h₁ h₂) : (Int32.ofIntLE n h₁ h₂).toInt16 = Int16.ofInt n := Int16.toInt.inj (by simp)
theorem Int64.toInt16_ofIntLE {n} (h₁ h₂) : (Int64.ofIntLE n h₁ h₂).toInt16 = Int16.ofInt n := Int16.toInt.inj (by simp)
theorem ISize.toInt16_ofIntLE {n} (h₁ h₂) : (ISize.ofIntLE n h₁ h₂).toInt16 = Int16.ofInt n := Int16.toInt.inj (by simp)

@[simp] theorem Int32.toInt16_ofBitVec (b) : (Int32.ofBitVec b).toInt16 = Int16.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int64.toInt16_ofBitVec (b) : (Int64.ofBitVec b).toInt16 = Int16.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem ISize.toInt16_ofBitVec (b) : (ISize.ofBitVec b).toInt16 = Int16.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int32.toInt16_ofNat' {n} : (Int32.ofNat n).toInt16 = Int16.ofNat n :=
  Int16.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem Int64.toInt16_ofNat' {n} : (Int64.ofNat n).toInt16 = Int16.ofNat n :=
  Int16.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem ISize.toInt16_ofNat' {n} : (ISize.ofNat n).toInt16 = Int16.ofNat n := by
  apply Int16.toBitVec.inj
  simp only [toBitVec_toInt16, toBitVec_ofNat', Int16.toBitVec_ofNat']
  rw [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_ofNat_of_le]
  all_goals cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem Int32.toInt16_ofInt {n} : (Int32.ofInt n).toInt16 = Int16.ofInt n :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem Int64.toInt16_ofInt {n} : (Int64.ofInt n).toInt16 = Int16.ofInt n :=
  Int16.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize.toInt16_ofInt {n} : (ISize.ofInt n).toInt16 = Int16.ofInt n := by
  apply Int16.toInt.inj
  simp only [toInt_toInt16, toInt_ofInt, Nat.reducePow, Int16.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd UInt16.size_dvd_usizeSize

@[simp] theorem Int32.toInt16_ofNat {n} : toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt16_ofNat'
@[simp] theorem Int64.toInt16_ofNat {n} : toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt16_ofNat'
@[simp] theorem ISize.toInt16_ofNat {n} : toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt16_ofNat'

theorem Int32.toInt16_ofIntTruncate {n : Int} (h₁ : -2 ^ 31 ≤ n) (h₂ : n < 2 ^ 31) :
    (Int32.ofIntTruncate n).toInt16 = Int16.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt16_ofIntLE]
theorem Int64.toInt16_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (Int64.ofIntTruncate n).toInt16 = Int16.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt16_ofIntLE]
theorem ISize.toInt16_ofIntTruncate {n : Int} (h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n)
    (h₂ : n < 2 ^ (System.Platform.numBits - 1)) : (ISize.ofIntTruncate n).toInt16 = Int16.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate, toInt16_ofIntLE]
  · exact toInt_minValue ▸ h₁
  · rw [toInt_maxValue]
    omega

theorem Int64.toInt32_ofIntLE {n} (h₁ h₂) : (Int64.ofIntLE n h₁ h₂).toInt32 = Int32.ofInt n := Int32.toInt.inj (by simp)
theorem ISize.toInt32_ofIntLE {n} (h₁ h₂) : (ISize.ofIntLE n h₁ h₂).toInt32 = Int32.ofInt n := Int32.toInt.inj (by simp)

@[simp] theorem Int64.toInt32_ofBitVec (b) : (Int64.ofBitVec b).toInt32 = Int32.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem ISize.toInt32_ofBitVec (b) : (ISize.ofBitVec b).toInt32 = Int32.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int64.toInt32_ofNat' {n} : (Int64.ofNat n).toInt32 = Int32.ofNat n :=
  Int32.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])
@[simp] theorem ISize.toInt32_ofNat' {n} : (ISize.ofNat n).toInt32 = Int32.ofNat n := by
  apply Int32.toBitVec.inj
  simp only [toBitVec_toInt32, toBitVec_ofNat', Int32.toBitVec_ofNat']
  rw [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_ofNat_of_le]
  all_goals cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem Int64.toInt32_ofInt {n} : (Int64.ofInt n).toInt32 = Int32.ofInt n :=
  Int32.toInt.inj (by simpa using Int.bmod_bmod_of_dvd (by decide))
@[simp] theorem ISize.toInt32_ofInt {n} : (ISize.ofInt n).toInt32 = Int32.ofInt n := by
  apply Int32.toInt.inj
  simp only [toInt_toInt32, toInt_ofInt, Nat.reducePow, Int32.toInt_ofInt]
  exact Int.bmod_bmod_of_dvd UInt32.size_dvd_usizeSize

@[simp] theorem Int64.toInt32_ofNat {n} : toInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt32_ofNat'
@[simp] theorem ISize.toInt32_ofNat {n} : toInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toInt32_ofNat'

theorem Int64.toInt32_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (Int64.ofIntTruncate n).toInt32 = Int32.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toInt32_ofIntLE]
theorem ISize.toInt32_ofIntTruncate {n : Int} (h₁ : -2 ^ (System.Platform.numBits - 1) ≤ n)
    (h₂ : n < 2 ^ (System.Platform.numBits - 1)) : (ISize.ofIntTruncate n).toInt32 = Int32.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate, toInt32_ofIntLE]
  · exact toInt_minValue ▸ h₁
  · rw [toInt_maxValue]
    omega

theorem Int64.toISize_ofIntLE {n} (h₁ h₂) : (Int64.ofIntLE n h₁ h₂).toISize = ISize.ofInt n :=
  ISize.toInt.inj (by simp [ISize.toInt_ofInt])

@[simp] theorem Int64.toISize_ofBitVec (b) : (Int64.ofBitVec b).toISize = ISize.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int64.toISize_ofNat' {n} : (Int64.ofNat n).toISize = ISize.ofNat n :=
  ISize.toBitVec.inj (by simp [BitVec.signExtend_eq_setWidth_of_le])

@[simp] theorem Int64.toISize_ofInt {n} : (Int64.ofInt n).toISize = ISize.ofInt n :=
 ISize.toInt.inj (by simpa [ISize.toInt_ofInt] using Int.bmod_bmod_of_dvd USize.size_dvd_uInt64Size)

@[simp] theorem Int64.toISize_ofNat {n} : toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := toISize_ofNat'

theorem Int64.toISize_ofIntTruncate {n : Int} (h₁ : -2 ^ 63 ≤ n) (h₂ : n < 2 ^ 63) :
    (Int64.ofIntTruncate n).toISize = ISize.ofInt n := by
  rw [← ofIntLE_eq_ofIntTruncate (h₁ := h₁) (h₂ := Int.le_of_lt_add_one h₂), toISize_ofIntLE]

@[simp] theorem Int8.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ := (rfl)
@[simp] theorem Int16.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ := (rfl)
@[simp] theorem Int32.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ := (rfl)
@[simp] theorem Int64.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ := (rfl)
@[simp] theorem ISize.toBitVec_minValue : minValue.toBitVec = BitVec.intMin _ :=
  BitVec.eq_of_toInt_eq (by rw [toInt_toBitVec, toInt_minValue,
    BitVec.toInt_intMin_of_pos (by cases System.Platform.numBits_eq <;> simp_all)])

@[simp] theorem Int16.toInt8_neg (x : Int16) : (-x).toInt8 = -x.toInt8 := Int8.toBitVec.inj (by simp)
@[simp] theorem Int32.toInt8_neg (x : Int32) : (-x).toInt8 = -x.toInt8 := Int8.toBitVec.inj (by simp)
@[simp] theorem Int64.toInt8_neg (x : Int64) : (-x).toInt8 = -x.toInt8 := Int8.toBitVec.inj (by simp)
@[simp] theorem ISize.toInt8_neg (x : ISize) : (-x).toInt8 = -x.toInt8 :=
  Int8.toBitVec.inj (by rw [toBitVec_toInt8, toBitVec_neg, Int8.toBitVec_neg, toBitVec_toInt8,
    BitVec.signExtend_neg_of_le (by cases System.Platform.numBits_eq <;> simp_all)])

@[simp] theorem Int32.toInt16_neg (x : Int32) : (-x).toInt16 = -x.toInt16 := Int16.toBitVec.inj (by simp)
@[simp] theorem Int64.toInt16_neg (x : Int64) : (-x).toInt16 = -x.toInt16 := Int16.toBitVec.inj (by simp)
@[simp] theorem ISize.toInt16_neg (x : ISize) : (-x).toInt16 = -x.toInt16 :=
  Int16.toBitVec.inj (by rw [toBitVec_toInt16, toBitVec_neg, Int16.toBitVec_neg, toBitVec_toInt16,
    BitVec.signExtend_neg_of_le (by cases System.Platform.numBits_eq <;> simp_all)])

@[simp] theorem Int64.toInt32_neg (x : Int64) : (-x).toInt32 = -x.toInt32 := Int32.toBitVec.inj (by simp)
@[simp] theorem ISize.toInt32_neg (x : ISize) : (-x).toInt32 = -x.toInt32 :=
  Int32.toBitVec.inj (by rw [toBitVec_toInt32, toBitVec_neg, Int32.toBitVec_neg, toBitVec_toInt32,
    BitVec.signExtend_neg_of_le (by cases System.Platform.numBits_eq <;> simp_all)])

@[simp] theorem Int64.toISize_neg (x : Int64) : (-x).toISize = -x.toISize := ISize.toBitVec.inj (by simp)

@[simp] theorem Int8.toInt16_neg_of_ne {x : Int8} (hx : x ≠ -128) : (-x).toInt16 = -x.toInt16 :=
  Int16.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int8.toBitVec.inj h)))

@[simp] theorem Int8.toInt32_neg_of_ne {x : Int8} (hx : x ≠ -128) : (-x).toInt32 = -x.toInt32 :=
  Int32.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int8.toBitVec.inj h)))
@[simp] theorem Int16.toInt32_neg_of_ne {x : Int16} (hx : x ≠ -32768) : (-x).toInt32 = -x.toInt32 :=
  Int32.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int16.toBitVec.inj h)))

@[simp] theorem Int8.toISize_neg_of_ne {x : Int8} (hx : x ≠ -128) : (-x).toISize = -x.toISize :=
  ISize.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int8.toBitVec.inj h)))
@[simp] theorem Int16.toISize_neg_of_ne {x : Int16} (hx : x ≠ -32768) : (-x).toISize = -x.toISize :=
  ISize.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int16.toBitVec.inj h)))
@[simp] theorem Int32.toISize_neg_of_ne {x : Int32} (hx : x ≠ -2147483648) : (-x).toISize = -x.toISize :=
  ISize.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int32.toBitVec.inj h)))

@[simp] theorem Int8.toInt64_neg_of_ne {x : Int8} (hx : x ≠ -128) : (-x).toInt64 = -x.toInt64 :=
  Int64.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int8.toBitVec.inj h)))
@[simp] theorem Int16.toInt64_neg_of_ne {x : Int16} (hx : x ≠ -32768) : (-x).toInt64 = -x.toInt64 :=
  Int64.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _ (fun h => hx (Int16.toBitVec.inj h)))
@[simp] theorem Int32.toInt64_neg_of_ne {x : Int32} (hx : x ≠ -2147483648) : (-x).toInt64 = -x.toInt64 :=
  Int64.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _  (fun h => hx (Int32.toBitVec.inj h)))
@[simp] theorem ISize.toInt64_neg_of_ne {x : ISize} (hx : x ≠ minValue) : (-x).toInt64 = -x.toInt64 :=
  Int64.toBitVec.inj (BitVec.signExtend_neg_of_ne_intMin _
    (fun h => hx (ISize.toBitVec.inj (h.trans toBitVec_minValue.symm))))

theorem Int8.toInt16_ofIntLE {n : Int} (h₁ h₂) :
    (Int8.ofIntLE n h₁ h₂).toInt16 = Int16.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int16.toInt.inj (by simp)
theorem Int8.toInt32_ofIntLE {n : Int} (h₁ h₂) :
    (Int8.ofIntLE n h₁ h₂).toInt32 = Int32.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int32.toInt.inj (by simp)
theorem Int8.toInt64_ofIntLE {n : Int} (h₁ h₂) :
    (Int8.ofIntLE n h₁ h₂).toInt64 = Int64.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int64.toInt.inj (by simp)
theorem Int8.toISize_ofIntLE {n : Int} (h₁ h₂) :
    (Int8.ofIntLE n h₁ h₂).toISize = ISize.ofIntLE n (Int.le_trans minValue.iSizeMinValue_le_toInt h₁)
      (Int.le_trans h₂ maxValue.toInt_le_iSizeMaxValue) :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int8.toInt16_ofBitVec (b) : (Int8.ofBitVec b).toInt16 = Int16.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int8.toInt32_ofBitVec (b) : (Int8.ofBitVec b).toInt32 = Int32.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int8.toInt64_ofBitVec (b) : (Int8.ofBitVec b).toInt64 = Int64.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int8.toISize_ofBitVec (b) : (Int8.ofBitVec b).toISize = ISize.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int8.toInt16_ofInt {n : Int} (h₁ : Int8.minValue.toInt ≤ n) (h₂ : n ≤ Int8.maxValue.toInt) :
    (Int8.ofInt n).toInt16 = Int16.ofInt n := by rw [← Int8.ofIntLE_eq_ofInt h₁ h₂, toInt16_ofIntLE, Int16.ofIntLE_eq_ofInt]
@[simp] theorem Int8.toInt32_ofInt {n : Int} (h₁ : Int8.minValue.toInt ≤ n) (h₂ : n ≤ Int8.maxValue.toInt) :
    (Int8.ofInt n).toInt32 = Int32.ofInt n := by rw [← Int8.ofIntLE_eq_ofInt h₁ h₂, toInt32_ofIntLE, Int32.ofIntLE_eq_ofInt]
@[simp] theorem Int8.toInt64_ofInt {n : Int} (h₁ : Int8.minValue.toInt ≤ n) (h₂ : n ≤ Int8.maxValue.toInt) :
    (Int8.ofInt n).toInt64 = Int64.ofInt n := by rw [← Int8.ofIntLE_eq_ofInt h₁ h₂, toInt64_ofIntLE, Int64.ofIntLE_eq_ofInt]
@[simp] theorem Int8.toISize_ofInt {n : Int} (h₁ : Int8.minValue.toInt ≤ n) (h₂ : n ≤ Int8.maxValue.toInt) :
    (Int8.ofInt n).toISize = ISize.ofInt n := by rw [← Int8.ofIntLE_eq_ofInt h₁ h₂, toISize_ofIntLE, ISize.ofIntLE_eq_ofInt]

@[simp] theorem Int8.toInt16_ofNat' {n : Nat} (h : n ≤ Int8.maxValue.toInt) :
    (Int8.ofNat n).toInt16 = Int16.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt16_ofInt (by simp [toInt_minValue]) h, Int16.ofInt_eq_ofNat]
@[simp] theorem Int8.toInt32_ofNat' {n : Nat} (h : n ≤ Int8.maxValue.toInt) :
    (Int8.ofNat n).toInt32 = Int32.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt32_ofInt (by simp [toInt_minValue]) h, Int32.ofInt_eq_ofNat]
@[simp] theorem Int8.toInt64_ofNat' {n : Nat} (h : n ≤ Int8.maxValue.toInt) :
    (Int8.ofNat n).toInt64 = Int64.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt64_ofInt (by simp [toInt_minValue]) h, Int64.ofInt_eq_ofNat]
@[simp] theorem Int8.toISize_ofNat' {n : Nat} (h : n ≤ Int8.maxValue.toInt) :
    (Int8.ofNat n).toISize = ISize.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize_ofInt (by simp [toInt_minValue]) h, ISize.ofInt_eq_ofNat]

@[simp] theorem Int8.toInt16_ofNat {n : Nat} (h : n ≤ 127) :
    toInt16 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int8.toInt16_ofNat' (by rw [toInt_maxValue]; omega)
@[simp] theorem Int8.toInt32_ofNat {n : Nat} (h : n ≤ 127) :
    toInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int8.toInt32_ofNat' (by rw [toInt_maxValue]; omega)
@[simp] theorem Int8.toInt64_ofNat {n : Nat} (h : n ≤ 127) :
    toInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int8.toInt64_ofNat' (by rw [toInt_maxValue]; omega)
@[simp] theorem Int8.toISize_ofNat {n : Nat} (h : n ≤ 127) :
    toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int8.toISize_ofNat' (by rw [toInt_maxValue]; omega)

theorem Int16.toInt32_ofIntLE {n : Int} (h₁ h₂) :
    (Int16.ofIntLE n h₁ h₂).toInt32 = Int32.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int32.toInt.inj (by simp)
theorem Int16.toInt64_ofIntLE {n : Int} (h₁ h₂) :
    (Int16.ofIntLE n h₁ h₂).toInt64 = Int64.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int64.toInt.inj (by simp)
theorem Int16.toISize_ofIntLE {n : Int} (h₁ h₂) :
    (Int16.ofIntLE n h₁ h₂).toISize = ISize.ofIntLE n (Int.le_trans minValue.iSizeMinValue_le_toInt h₁)
      (Int.le_trans h₂ maxValue.toInt_le_iSizeMaxValue) :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int16.toInt32_ofBitVec (b) : (Int16.ofBitVec b).toInt32 = Int32.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int16.toInt64_ofBitVec (b) : (Int16.ofBitVec b).toInt64 = Int64.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int16.toISize_ofBitVec (b) : (Int16.ofBitVec b).toISize = ISize.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int16.toInt32_ofInt {n : Int} (h₁ : Int16.minValue.toInt ≤ n) (h₂ : n ≤ Int16.maxValue.toInt) :
    (Int16.ofInt n).toInt32 = Int32.ofInt n := by rw [← Int16.ofIntLE_eq_ofInt h₁ h₂, toInt32_ofIntLE, Int32.ofIntLE_eq_ofInt]
@[simp] theorem Int16.toInt64_ofInt {n : Int} (h₁ : Int16.minValue.toInt ≤ n) (h₂ : n ≤ Int16.maxValue.toInt) :
    (Int16.ofInt n).toInt64 = Int64.ofInt n := by rw [← Int16.ofIntLE_eq_ofInt h₁ h₂, toInt64_ofIntLE, Int64.ofIntLE_eq_ofInt]
@[simp] theorem Int16.toISize_ofInt {n : Int} (h₁ : Int16.minValue.toInt ≤ n) (h₂ : n ≤ Int16.maxValue.toInt) :
    (Int16.ofInt n).toISize = ISize.ofInt n := by rw [← Int16.ofIntLE_eq_ofInt h₁ h₂, toISize_ofIntLE, ISize.ofIntLE_eq_ofInt]

@[simp] theorem Int16.toInt32_ofNat' {n : Nat} (h : n ≤ Int16.maxValue.toInt) :
    (Int16.ofNat n).toInt32 = Int32.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt32_ofInt (by simp [toInt_minValue]) h, Int32.ofInt_eq_ofNat]
@[simp] theorem Int16.toInt64_ofNat' {n : Nat} (h : n ≤ Int16.maxValue.toInt) :
    (Int16.ofNat n).toInt64 = Int64.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt64_ofInt (by simp [toInt_minValue]) h, Int64.ofInt_eq_ofNat]
@[simp] theorem Int16.toISize_ofNat' {n : Nat} (h : n ≤ Int16.maxValue.toInt) :
    (Int16.ofNat n).toISize = ISize.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize_ofInt (by simp [toInt_minValue]) h, ISize.ofInt_eq_ofNat]

@[simp] theorem Int16.toInt32_ofNat {n : Nat} (h : n ≤ 32767) :
    toInt32 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int16.toInt32_ofNat' (by rw [toInt_maxValue]; omega)
@[simp] theorem Int16.toInt64_ofNat {n : Nat} (h : n ≤ 32767) :
    toInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int16.toInt64_ofNat' (by rw [toInt_maxValue]; omega)
@[simp] theorem Int16.toISize_ofNat {n : Nat} (h : n ≤ 32767) :
    toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int16.toISize_ofNat' (by rw [toInt_maxValue]; omega)

theorem Int32.toInt64_ofIntLE {n : Int} (h₁ h₂) :
    (Int32.ofIntLE n h₁ h₂).toInt64 = Int64.ofIntLE n (Int.le_trans (by decide) h₁) (Int.le_trans h₂ (by decide)) :=
  Int64.toInt.inj (by simp)
theorem Int32.toISize_ofIntLE {n : Int} (h₁ h₂) :
    (Int32.ofIntLE n h₁ h₂).toISize = ISize.ofIntLE n (Int.le_trans minValue.iSizeMinValue_le_toInt h₁)
      (Int.le_trans h₂ maxValue.toInt_le_iSizeMaxValue) :=
  ISize.toInt.inj (by simp)

@[simp] theorem Int32.toInt64_ofBitVec (b) : (Int32.ofBitVec b).toInt64 = Int64.ofBitVec (b.signExtend _) := (rfl)
@[simp] theorem Int32.toISize_ofBitVec (b) : (Int32.ofBitVec b).toISize = ISize.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem Int32.toInt64_ofInt {n : Int} (h₁ : Int32.minValue.toInt ≤ n) (h₂ : n ≤ Int32.maxValue.toInt) :
    (Int32.ofInt n).toInt64 = Int64.ofInt n := by rw [← Int32.ofIntLE_eq_ofInt h₁ h₂, toInt64_ofIntLE, Int64.ofIntLE_eq_ofInt]
@[simp] theorem Int32.toISize_ofInt {n : Int} (h₁ : Int32.minValue.toInt ≤ n) (h₂ : n ≤ Int32.maxValue.toInt) :
    (Int32.ofInt n).toISize = ISize.ofInt n := by rw [← Int32.ofIntLE_eq_ofInt h₁ h₂, toISize_ofIntLE, ISize.ofIntLE_eq_ofInt]

@[simp] theorem Int32.toInt64_ofNat' {n : Nat} (h : n ≤ Int32.maxValue.toInt) :
    (Int32.ofNat n).toInt64 = Int64.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt64_ofInt (by simp [toInt_minValue]) h, Int64.ofInt_eq_ofNat]
@[simp] theorem Int32.toISize_ofNat' {n : Nat} (h : n ≤ Int32.maxValue.toInt) :
    (Int32.ofNat n).toISize = ISize.ofNat n := by
  rw [← ofInt_eq_ofNat, toISize_ofInt (by simp [toInt_minValue]) h, ISize.ofInt_eq_ofNat]

@[simp] theorem Int32.toInt64_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int32.toInt64_ofNat' (by rw [toInt_maxValue]; omega)
@[simp] theorem Int32.toISize_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toISize (no_index (OfNat.ofNat n)) = OfNat.ofNat n := Int32.toISize_ofNat' (by rw [toInt_maxValue]; omega)

theorem ISize.toInt64_ofIntLE {n : Int} (h₁ h₂) :
    (ISize.ofIntLE n h₁ h₂).toInt64 = Int64.ofIntLE n (Int.le_trans minValue.int64MinValue_le_toInt h₁)
      (Int.le_trans h₂ maxValue.toInt_le_int64MaxValue) :=
  Int64.toInt.inj (by simp)

@[simp] theorem ISize.toInt64_ofBitVec (b) : (ISize.ofBitVec b).toInt64 = Int64.ofBitVec (b.signExtend _) := (rfl)

@[simp] theorem ISize.toInt64_ofInt {n : Int} (h₁ : ISize.minValue.toInt ≤ n) (h₂ : n ≤ ISize.maxValue.toInt) :
    (ISize.ofInt n).toInt64 = Int64.ofInt n := by rw [← ISize.ofIntLE_eq_ofInt h₁ h₂, toInt64_ofIntLE, Int64.ofIntLE_eq_ofInt]

@[simp] theorem ISize.toInt64_ofNat' {n : Nat} (h : n ≤ ISize.maxValue.toInt) :
    (ISize.ofNat n).toInt64 = Int64.ofNat n := by
  rw [← ofInt_eq_ofNat, toInt64_ofInt _ h, Int64.ofInt_eq_ofNat]
  refine Int.le_trans ?_ (Int.zero_le_ofNat _)
  cases System.Platform.numBits_eq <;> simp_all [ISize.toInt_minValue]

@[simp] theorem ISize.toInt64_ofNat {n : Nat} (h : n ≤ 2147483647) :
    toInt64 (no_index (OfNat.ofNat n)) = OfNat.ofNat n :=
  ISize.toInt64_ofNat' (by rw [toInt_maxValue]; cases System.Platform.numBits_eq <;> simp_all <;> omega)

@[simp] theorem Int8.ofIntLE_bitVecToInt (n : BitVec 8) :
    Int8.ofIntLE n.toInt (by exact n.le_toInt) (by exact n.toInt_le) = Int8.ofBitVec n :=
  Int8.toBitVec.inj (by simp)
@[simp] theorem Int16.ofIntLE_bitVecToInt (n : BitVec 16) :
    Int16.ofIntLE n.toInt (by exact n.le_toInt) (by exact n.toInt_le) = Int16.ofBitVec n :=
  Int16.toBitVec.inj (by simp)
@[simp] theorem Int32.ofIntLE_bitVecToInt (n : BitVec 32) :
    Int32.ofIntLE n.toInt (by exact n.le_toInt) (by exact n.toInt_le) = Int32.ofBitVec n :=
  Int32.toBitVec.inj (by simp)
@[simp] theorem Int64.ofIntLE_bitVecToInt (n : BitVec 64) :
    Int64.ofIntLE n.toInt (by exact n.le_toInt) (by exact n.toInt_le) = Int64.ofBitVec n :=
  Int64.toBitVec.inj (by simp)
@[simp] theorem ISize.ofIntLE_bitVecToInt (n : BitVec System.Platform.numBits) :
    ISize.ofIntLE n.toInt (toInt_minValue ▸ n.le_toInt)
    (toInt_maxValue ▸ n.toInt_le) = ISize.ofBitVec n :=
  ISize.toBitVec.inj (by simp)

theorem Int8.ofBitVec_ofNatLT (n : Nat) (hn) : Int8.ofBitVec (BitVec.ofNatLT n hn) = Int8.ofNat n :=
  Int8.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat hn])
theorem Int16.ofBitVec_ofNatLT (n : Nat) (hn) : Int16.ofBitVec (BitVec.ofNatLT n hn) = Int16.ofNat n :=
  Int16.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat hn])
theorem Int32.ofBitVec_ofNatLT (n : Nat) (hn) : Int32.ofBitVec (BitVec.ofNatLT n hn) = Int32.ofNat n :=
  Int32.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat hn])
theorem Int64.ofBitVec_ofNatLT (n : Nat) (hn) : Int64.ofBitVec (BitVec.ofNatLT n hn) = Int64.ofNat n :=
  Int64.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat hn])
theorem ISize.ofBitVec_ofNatLT (n : Nat) (hn) : ISize.ofBitVec (BitVec.ofNatLT n hn) = ISize.ofNat n :=
  ISize.toBitVec.inj (by simp [BitVec.ofNatLT_eq_ofNat hn])

@[simp] theorem Int8.ofBitVec_ofNat (n : Nat) : Int8.ofBitVec (BitVec.ofNat 8 n) = Int8.ofNat n := (rfl)
@[simp] theorem Int16.ofBitVec_ofNat (n : Nat) : Int16.ofBitVec (BitVec.ofNat 16 n) = Int16.ofNat n := (rfl)
@[simp] theorem Int32.ofBitVec_ofNat (n : Nat) : Int32.ofBitVec (BitVec.ofNat 32 n) = Int32.ofNat n := (rfl)
@[simp] theorem Int64.ofBitVec_ofNat (n : Nat) : Int64.ofBitVec (BitVec.ofNat 64 n) = Int64.ofNat n := (rfl)
@[simp] theorem ISize.ofBitVec_ofNat (n : Nat) : ISize.ofBitVec (BitVec.ofNat System.Platform.numBits n) = ISize.ofNat n := (rfl)

@[simp] theorem Int8.ofBitVec_ofInt (n : Int) : Int8.ofBitVec (BitVec.ofInt 8 n) = Int8.ofInt n := (rfl)
@[simp] theorem Int16.ofBitVec_ofInt (n : Int) : Int16.ofBitVec (BitVec.ofInt 16 n) = Int16.ofInt n := (rfl)
@[simp] theorem Int32.ofBitVec_ofInt (n : Int) : Int32.ofBitVec (BitVec.ofInt 32 n) = Int32.ofInt n := (rfl)
@[simp] theorem Int64.ofBitVec_ofInt (n : Int) : Int64.ofBitVec (BitVec.ofInt 64 n) = Int64.ofInt n := (rfl)
@[simp] theorem ISize.ofBitVec_ofInt (n : Int) : ISize.ofBitVec (BitVec.ofInt System.Platform.numBits n) = ISize.ofInt n := (rfl)

@[simp] theorem Int8.ofNat_bitVecToNat (n : BitVec 8) : Int8.ofNat n.toNat = Int8.ofBitVec n :=
  Int8.toBitVec.inj (by simp)
@[simp] theorem Int16.ofNat_bitVecToNat (n : BitVec 16) : Int16.ofNat n.toNat = Int16.ofBitVec n :=
  Int16.toBitVec.inj (by simp)
@[simp] theorem Int32.ofNat_bitVecToNat (n : BitVec 32) : Int32.ofNat n.toNat = Int32.ofBitVec n :=
  Int32.toBitVec.inj (by simp)
@[simp] theorem Int64.ofNat_bitVecToNat (n : BitVec 64) : Int64.ofNat n.toNat = Int64.ofBitVec n :=
  Int64.toBitVec.inj (by simp)
@[simp] theorem ISize.ofNat_bitVecToNat (n : BitVec System.Platform.numBits) : ISize.ofNat n.toNat = ISize.ofBitVec n :=
  ISize.toBitVec.inj (by simp)

@[simp] theorem Int8.ofInt_bitVecToInt (n : BitVec 8) : Int8.ofInt n.toInt = Int8.ofBitVec n :=
  Int8.toBitVec.inj (by simp)
@[simp] theorem Int16.ofInt_bitVecToInt (n : BitVec 16) : Int16.ofInt n.toInt = Int16.ofBitVec n :=
  Int16.toBitVec.inj (by simp)
@[simp] theorem Int32.ofInt_bitVecToInt (n : BitVec 32) : Int32.ofInt n.toInt = Int32.ofBitVec n :=
  Int32.toBitVec.inj (by simp)
@[simp] theorem Int64.ofInt_bitVecToInt (n : BitVec 64) : Int64.ofInt n.toInt = Int64.ofBitVec n :=
  Int64.toBitVec.inj (by simp)
@[simp] theorem ISize.ofInt_bitVecToInt (n : BitVec System.Platform.numBits) : ISize.ofInt n.toInt = ISize.ofBitVec n :=
  ISize.toBitVec.inj (by simp)

@[simp] theorem Int8.ofIntTruncate_bitVecToInt (n : BitVec 8) : Int8.ofIntTruncate n.toInt = Int8.ofBitVec n :=
  Int8.toBitVec.inj (by simp [toBitVec_ofIntTruncate (n.le_toInt) (n.toInt_le)])
@[simp] theorem Int16.ofIntTruncate_bitVecToInt (n : BitVec 16) : Int16.ofIntTruncate n.toInt = Int16.ofBitVec n :=
  Int16.toBitVec.inj (by simp [toBitVec_ofIntTruncate (n.le_toInt) (n.toInt_le)])
@[simp] theorem Int32.ofIntTruncate_bitVecToInt (n : BitVec 32) : Int32.ofIntTruncate n.toInt = Int32.ofBitVec n :=
  Int32.toBitVec.inj (by simp [toBitVec_ofIntTruncate (n.le_toInt) (n.toInt_le)])
@[simp] theorem Int64.ofIntTruncate_bitVecToInt (n : BitVec 64) : Int64.ofIntTruncate n.toInt = Int64.ofBitVec n :=
  Int64.toBitVec.inj (by simp [toBitVec_ofIntTruncate (n.le_toInt) (n.toInt_le)])
@[simp] theorem ISize.ofIntTruncate_bitVecToInt (n : BitVec System.Platform.numBits) : ISize.ofIntTruncate n.toInt = ISize.ofBitVec n :=
  ISize.toBitVec.inj (by simp [toBitVec_ofIntTruncate (toInt_minValue ▸ n.le_toInt)
    (toInt_maxValue ▸ n.toInt_le) ])

@[simp] theorem Int8.toInt_neg (n : Int8) : (-n).toInt = (-n.toInt).bmod (2 ^ 8) := BitVec.toInt_neg
@[simp] theorem Int16.toInt_neg (n : Int16) : (-n).toInt = (-n.toInt).bmod (2 ^ 16) := BitVec.toInt_neg
@[simp] theorem Int32.toInt_neg (n : Int32) : (-n).toInt = (-n.toInt).bmod (2 ^ 32) := BitVec.toInt_neg
@[simp] theorem Int64.toInt_neg (n : Int64) : (-n).toInt = (-n.toInt).bmod (2 ^ 64) := BitVec.toInt_neg
-- Simp on this seems to do more harm than good when numeric literals are involved
theorem ISize.toInt_neg (n : ISize) : (-n).toInt = (-n.toInt).bmod (2 ^ System.Platform.numBits) := BitVec.toInt_neg

@[simp] theorem Int8.toNatClampNeg_eq_zero_iff {n : Int8} : n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le, toInt_zero]
@[simp] theorem Int16.toNatClampNeg_eq_zero_iff {n : Int16} : n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le, toInt_zero]
@[simp] theorem Int32.toNatClampNeg_eq_zero_iff {n : Int32} : n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le, toInt_zero]
@[simp] theorem Int64.toNatClampNeg_eq_zero_iff {n : Int64} : n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le, toInt_zero]
@[simp] theorem ISize.toNatClampNeg_eq_zero_iff {n : ISize} : n.toNatClampNeg = 0 ↔ n ≤ 0 := by
  rw [toNatClampNeg, Int.toNat_eq_zero, le_iff_toInt_le, toInt_zero]

@[simp] protected theorem Int8.not_le {n m : Int8} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]
@[simp] protected theorem Int16.not_le {n m : Int16} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]
@[simp] protected theorem Int32.not_le {n m : Int32} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]
@[simp] protected theorem Int64.not_le {n m : Int64} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]
@[simp] protected theorem ISize.not_le {n m : ISize} : ¬n ≤ m ↔ m < n := by simp [le_iff_toInt_le, lt_iff_toInt_lt]

@[simp] theorem Int8.neg_nonpos_iff (n : Int8) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero (by decide)]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]
@[simp] theorem Int16.neg_nonpos_iff (n : Int16) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero (by decide)]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]
@[simp] theorem Int32.neg_nonpos_iff (n : Int32) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero (by decide)]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]
@[simp] theorem Int64.neg_nonpos_iff (n : Int64) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero (by decide)]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]
@[simp] theorem ISize.neg_nonpos_iff (n : ISize) : -n ≤ 0 ↔ n = minValue ∨ 0 ≤ n := by
  rw [le_iff_toBitVec_sle, toBitVec_zero, toBitVec_neg, BitVec.neg_sle_zero System.Platform.numBits_pos]
  simp [← toBitVec_inj, le_iff_toBitVec_sle, BitVec.intMin_eq_neg_two_pow]

@[simp] theorem Int8.toNatClampNeg_pos_iff (n : Int8) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]
@[simp] theorem Int16.toNatClampNeg_pos_iff (n : Int16) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]
@[simp] theorem Int32.toNatClampNeg_pos_iff (n : Int32) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]
@[simp] theorem Int64.toNatClampNeg_pos_iff (n : Int64) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]
@[simp] theorem ISize.toNatClampNeg_pos_iff (n : ISize) : 0 < n.toNatClampNeg ↔ 0 < n := by simp [Nat.pos_iff_ne_zero]

@[simp] theorem Int8.toInt_div (a b : Int8) : (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ 8) := by
  rw [← toInt_toBitVec, Int8.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int16.toInt_div (a b : Int16) : (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ 16) := by
  rw [← toInt_toBitVec, Int16.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int32.toInt_div (a b : Int32) : (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ 32) := by
  rw [← toInt_toBitVec, Int32.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int64.toInt_div (a b : Int64) : (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ 64) := by
  rw [← toInt_toBitVec, Int64.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem ISize.toInt_div (a b : ISize) : (a / b).toInt = (a.toInt.tdiv b.toInt).bmod (2 ^ System.Platform.numBits) := by
  rw [← toInt_toBitVec, ISize.toBitVec_div, BitVec.toInt_sdiv, toInt_toBitVec, toInt_toBitVec]

theorem Int8.toInt_div_of_ne_left (a b : Int8) (h : a ≠ minValue) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int8.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj] using h)
theorem Int16.toInt_div_of_ne_left (a b : Int16) (h : a ≠ minValue) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int16.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj] using h)
theorem Int32.toInt_div_of_ne_left (a b : Int32) (h : a ≠ minValue) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int32.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj] using h)
theorem Int64.toInt_div_of_ne_left (a b : Int64) (h : a ≠ minValue) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int64.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj] using h)
theorem ISize.toInt_div_of_ne_left (a b : ISize) (h : a ≠ minValue) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, ISize.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inl (by simpa [← toBitVec_inj, BitVec.intMin_eq_neg_two_pow] using h)

theorem Int8.toInt_div_of_ne_right (a b : Int8) (h : b ≠ -1) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int8.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)
theorem Int16.toInt_div_of_ne_right (a b : Int16) (h : b ≠ -1) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int16.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)
theorem Int32.toInt_div_of_ne_right (a b : Int32) (h : b ≠ -1) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int32.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)
theorem Int64.toInt_div_of_ne_right (a b : Int64) (h : b ≠ -1) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, Int64.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)
theorem ISize.toInt_div_of_ne_right (a b : ISize) (h : b ≠ -1) : (a / b).toInt = a.toInt.tdiv b.toInt := by
  rw [← toInt_toBitVec, ISize.toBitVec_div, BitVec.toInt_sdiv_of_ne_or_ne, toInt_toBitVec, toInt_toBitVec]
  exact Or.inr (by simpa [← toBitVec_inj] using h)

theorem Int8.toInt16_ne_minValue (a : Int8) : a.toInt16 ≠ Int16.minValue :=
  have := a.le_toInt; by simp [← Int16.toInt_inj, Int16.toInt_minValue]; omega
theorem Int8.toInt32_ne_minValue (a : Int8) : a.toInt32 ≠ Int32.minValue :=
  have := a.le_toInt; by simp [← Int32.toInt_inj, Int32.toInt_minValue]; omega
theorem Int8.toInt64_ne_minValue (a : Int8) : a.toInt64 ≠ Int64.minValue :=
  have := a.le_toInt; by simp [← Int64.toInt_inj, Int64.toInt_minValue]; omega
theorem Int8.toISize_ne_minValue (a : Int8) : a.toISize ≠ ISize.minValue :=
  have := a.le_toInt; have := ISize.toInt_minValue_le; by simp [← ISize.toInt_inj]; omega

theorem Int16.toInt32_ne_minValue (a : Int16) : a.toInt32 ≠ Int32.minValue :=
  have := a.le_toInt; by simp [← Int32.toInt_inj, Int32.toInt_minValue]; omega
theorem Int16.toInt64_ne_minValue (a : Int16) : a.toInt64 ≠ Int64.minValue :=
  have := a.le_toInt; by simp [← Int64.toInt_inj, Int64.toInt_minValue]; omega
theorem Int16.toISize_ne_minValue (a : Int16) : a.toISize ≠ ISize.minValue :=
  have := a.le_toInt; have := ISize.toInt_minValue_le; by simp [← ISize.toInt_inj]; omega

theorem Int32.toInt64_ne_minValue (a : Int32) : a.toInt64 ≠ Int64.minValue :=
  have := a.le_toInt; by simp [← Int64.toInt_inj, Int64.toInt_minValue]; omega
theorem Int32.toISize_ne_minValue (a : Int32) (ha : a ≠ minValue) : a.toISize ≠ ISize.minValue := by
  have := a.le_toInt
  have := ISize.toInt_minValue_le
  simp [← ISize.toInt_inj, ← Int32.toInt_inj] at ⊢ ha; omega

theorem ISize.toInt64_ne_minValue (a : ISize) (ha : a ≠ minValue) : a.toInt64 ≠ Int64.minValue := by
  have := a.minValue_le_toInt
  have : -2 ^ 63 ≤ minValue.toInt := minValue.le_toInt
  simp [← Int64.toInt_inj, ← ISize.toInt_inj] at *; omega

theorem Int8.toInt16_ne_neg_one (a : Int8) (ha : a ≠ -1) : a.toInt16 ≠ -1 :=
  ne_of_apply_ne Int16.toInt8 (by simpa using ha)
theorem Int8.toInt32_ne_neg_one (a : Int8) (ha : a ≠ -1) : a.toInt32 ≠ -1 :=
  ne_of_apply_ne Int32.toInt8 (by simpa using ha)
theorem Int8.toInt64_ne_neg_one (a : Int8) (ha : a ≠ -1) : a.toInt64 ≠ -1 :=
  ne_of_apply_ne Int64.toInt8 (by simpa using ha)
theorem Int8.toISize_ne_neg_one (a : Int8) (ha : a ≠ -1) : a.toISize ≠ -1 :=
  ne_of_apply_ne ISize.toInt8 (by simpa using ha)

theorem Int16.toInt32_ne_neg_one (a : Int16) (ha : a ≠ -1) : a.toInt32 ≠ -1 :=
  ne_of_apply_ne Int32.toInt16 (by simpa using ha)
theorem Int16.toInt64_ne_neg_one (a : Int16) (ha : a ≠ -1) : a.toInt64 ≠ -1 :=
  ne_of_apply_ne Int64.toInt16 (by simpa using ha)
theorem Int16.toISize_ne_neg_one (a : Int16) (ha : a ≠ -1) : a.toISize ≠ -1 :=
  ne_of_apply_ne ISize.toInt16 (by simpa using ha)

theorem Int32.toInt64_ne_neg_one (a : Int32) (ha : a ≠ -1) : a.toInt64 ≠ -1 :=
  ne_of_apply_ne Int64.toInt32 (by simpa using ha)
theorem Int32.toISize_ne_neg_one (a : Int32) (ha : a ≠ -1) : a.toISize ≠ -1 :=
  ne_of_apply_ne ISize.toInt32 (by simpa using ha)

theorem ISize.toInt64_ne_neg_one (a : ISize) (ha : a ≠ -1) : a.toInt64 ≠ -1 :=
  ne_of_apply_ne Int64.toISize (by simpa using ha)

theorem Int8.toInt16_div_of_ne_left (a b : Int8) (ha : a ≠ minValue) : (a / b).toInt16 = a.toInt16 / b.toInt16 :=
  Int16.toInt_inj.1 (by rw [toInt_toInt16, toInt_div_of_ne_left _ _ ha,
    Int16.toInt_div_of_ne_left _ _ a.toInt16_ne_minValue, toInt_toInt16, toInt_toInt16])
theorem Int8.toInt32_div_of_ne_left (a b : Int8) (ha : a ≠ minValue) : (a / b).toInt32 = a.toInt32 / b.toInt32 :=
  Int32.toInt_inj.1 (by rw [toInt_toInt32, toInt_div_of_ne_left _ _ ha,
    Int32.toInt_div_of_ne_left _ _ a.toInt32_ne_minValue, toInt_toInt32, toInt_toInt32])
theorem Int8.toInt64_div_of_ne_left (a b : Int8) (ha : a ≠ minValue) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_left _ _ ha,
    Int64.toInt_div_of_ne_left _ _ a.toInt64_ne_minValue, toInt_toInt64, toInt_toInt64])
theorem Int8.toISize_div_of_ne_left (a b : Int8) (ha : a ≠ minValue) : (a / b).toISize = a.toISize / b.toISize :=
  ISize.toInt_inj.1 (by rw [toInt_toISize, toInt_div_of_ne_left _ _ ha,
    ISize.toInt_div_of_ne_left _ _ a.toISize_ne_minValue, toInt_toISize, toInt_toISize])

theorem Int16.toInt32_div_of_ne_left (a b : Int16) (ha : a ≠ minValue) : (a / b).toInt32 = a.toInt32 / b.toInt32 :=
  Int32.toInt_inj.1 (by rw [toInt_toInt32, toInt_div_of_ne_left _ _ ha,
    Int32.toInt_div_of_ne_left _ _ a.toInt32_ne_minValue, toInt_toInt32, toInt_toInt32])
theorem Int16.toInt64_div_of_ne_left (a b : Int16) (ha : a ≠ minValue) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_left _ _ ha,
    Int64.toInt_div_of_ne_left _ _ a.toInt64_ne_minValue, toInt_toInt64, toInt_toInt64])
theorem Int16.toISize_div_of_ne_left (a b : Int16) (ha : a ≠ minValue) : (a / b).toISize = a.toISize / b.toISize :=
  ISize.toInt_inj.1 (by rw [toInt_toISize, toInt_div_of_ne_left _ _ ha,
    ISize.toInt_div_of_ne_left _ _ a.toISize_ne_minValue, toInt_toISize, toInt_toISize])

theorem Int32.toInt64_div_of_ne_left (a b : Int32) (ha : a ≠ minValue) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_left _ _ ha,
    Int64.toInt_div_of_ne_left _ _ a.toInt64_ne_minValue, toInt_toInt64, toInt_toInt64])
theorem Int32.toISize_div_of_ne_left (a b : Int32) (ha : a ≠ minValue) : (a / b).toISize = a.toISize / b.toISize :=
  ISize.toInt_inj.1 (by rw [toInt_toISize, toInt_div_of_ne_left _ _ ha,
    ISize.toInt_div_of_ne_left _ _ (a.toISize_ne_minValue ha), toInt_toISize, toInt_toISize])

theorem ISize.toInt64_div_of_ne_left (a b : ISize) (ha : a ≠ minValue) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_left _ _ ha,
    Int64.toInt_div_of_ne_left _ _ (a.toInt64_ne_minValue ha), toInt_toInt64, toInt_toInt64])

theorem Int8.toInt16_div_of_ne_right (a b : Int8) (hb : b ≠ -1) : (a / b).toInt16 = a.toInt16 / b.toInt16 :=
  Int16.toInt_inj.1 (by rw [toInt_toInt16, toInt_div_of_ne_right _ _ hb,
    Int16.toInt_div_of_ne_right _ _ (b.toInt16_ne_neg_one hb), toInt_toInt16, toInt_toInt16])
theorem Int8.toInt32_div_of_ne_right (a b : Int8) (hb : b ≠ -1) : (a / b).toInt32 = a.toInt32 / b.toInt32 :=
  Int32.toInt_inj.1 (by rw [toInt_toInt32, toInt_div_of_ne_right _ _ hb,
    Int32.toInt_div_of_ne_right _ _ (b.toInt32_ne_neg_one hb), toInt_toInt32, toInt_toInt32])
theorem Int8.toInt64_div_of_ne_right (a b : Int8) (hb : b ≠ -1) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_right _ _ hb,
    Int64.toInt_div_of_ne_right _ _ (b.toInt64_ne_neg_one hb), toInt_toInt64, toInt_toInt64])
theorem Int8.toISize_div_of_ne_right (a b : Int8) (hb : b ≠ -1) : (a / b).toISize = a.toISize / b.toISize :=
  ISize.toInt_inj.1 (by rw [toInt_toISize, toInt_div_of_ne_right _ _ hb,
    ISize.toInt_div_of_ne_right _ _ (b.toISize_ne_neg_one hb), toInt_toISize, toInt_toISize])

theorem Int16.toInt32_div_of_ne_right (a b : Int16) (hb : b ≠ -1) : (a / b).toInt32 = a.toInt32 / b.toInt32 :=
  Int32.toInt_inj.1 (by rw [toInt_toInt32, toInt_div_of_ne_right _ _ hb,
    Int32.toInt_div_of_ne_right _ _ (b.toInt32_ne_neg_one hb), toInt_toInt32, toInt_toInt32])
theorem Int16.toInt64_div_of_ne_right (a b : Int16) (hb : b ≠ -1) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_right _ _ hb,
    Int64.toInt_div_of_ne_right _ _ (b.toInt64_ne_neg_one hb), toInt_toInt64, toInt_toInt64])
theorem Int16.toISize_div_of_ne_right (a b : Int16) (hb : b ≠ -1) : (a / b).toISize = a.toISize / b.toISize :=
  ISize.toInt_inj.1 (by rw [toInt_toISize, toInt_div_of_ne_right _ _ hb,
    ISize.toInt_div_of_ne_right _ _ (b.toISize_ne_neg_one hb), toInt_toISize, toInt_toISize])

theorem Int32.toInt64_div_of_ne_right (a b : Int32) (hb : b ≠ -1) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_right _ _ hb,
    Int64.toInt_div_of_ne_right _ _ (b.toInt64_ne_neg_one hb), toInt_toInt64, toInt_toInt64])
theorem Int32.toISize_div_of_ne_right (a b : Int32) (hb : b ≠ -1) : (a / b).toISize = a.toISize / b.toISize :=
  ISize.toInt_inj.1 (by rw [toInt_toISize, toInt_div_of_ne_right _ _ hb,
    ISize.toInt_div_of_ne_right _ _ (b.toISize_ne_neg_one hb), toInt_toISize, toInt_toISize])

theorem ISize.toInt64_div_of_ne_right (a b : ISize) (hb : b ≠ -1) : (a / b).toInt64 = a.toInt64 / b.toInt64 :=
  Int64.toInt_inj.1 (by rw [toInt_toInt64, toInt_div_of_ne_right _ _ hb,
    Int64.toInt_div_of_ne_right _ _ (b.toInt64_ne_neg_one hb), toInt_toInt64, toInt_toInt64])

@[simp] theorem Int8.minValue_div_neg_one : minValue / -1 = minValue := (rfl)
@[simp] theorem Int16.minValue_div_neg_one : minValue / -1 = minValue := (rfl)
@[simp] theorem Int32.minValue_div_neg_one : minValue / -1 = minValue := (rfl)
@[simp] theorem Int64.minValue_div_neg_one : minValue / -1 = minValue := (rfl)
@[simp] theorem ISize.minValue_div_neg_one : minValue / -1 = minValue :=
  ISize.toBitVec_inj.1 (by simpa [BitVec.intMin_eq_neg_two_pow] using BitVec.intMin_sdiv_neg_one)

@[simp] theorem Int8.toInt_add (a b : Int8) : (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ 8) := by
  rw [← toInt_toBitVec, Int8.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int16.toInt_add (a b : Int16) : (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ 16) := by
  rw [← toInt_toBitVec, Int16.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int32.toInt_add (a b : Int32) : (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ 32) := by
  rw [← toInt_toBitVec, Int32.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int64.toInt_add (a b : Int64) : (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ 64) := by
  rw [← toInt_toBitVec, Int64.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem ISize.toInt_add (a b : ISize) : (a + b).toInt = (a.toInt + b.toInt).bmod (2 ^ System.Platform.numBits) := by
  rw [← toInt_toBitVec, ISize.toBitVec_add, BitVec.toInt_add, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem Int16.toInt8_add (a b : Int16) : (a + b).toInt8 = a.toInt8 + b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem Int32.toInt8_add (a b : Int32) : (a + b).toInt8 = a.toInt8 + b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem Int32.toInt16_add (a b : Int32) : (a + b).toInt16 = a.toInt16 + b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem ISize.toInt8_add (a b : ISize) : (a + b).toInt8 = a.toInt8 + b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem ISize.toInt16_add (a b : ISize) : (a + b).toInt16 = a.toInt16 + b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem ISize.toInt32_add (a b : ISize) : (a + b).toInt32 = a.toInt32 + b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem Int64.toInt8_add (a b : Int64) : (a + b).toInt8 = a.toInt8 + b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem Int64.toInt16_add (a b : Int64) : (a + b).toInt16 = a.toInt16 + b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem Int64.toInt32_add (a b : Int64) : (a + b).toInt32 = a.toInt32 + b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])
@[simp] theorem Int64.toISize_add (a b : Int64) : (a + b).toISize = a.toISize + b.toISize :=
  ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_add])

@[simp] theorem Int8.toInt_mul (a b : Int8) : (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ 8) := by
  rw [← toInt_toBitVec, Int8.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int16.toInt_mul (a b : Int16) : (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ 16) := by
  rw [← toInt_toBitVec, Int16.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int32.toInt_mul (a b : Int32) : (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ 32) := by
  rw [← toInt_toBitVec, Int32.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int64.toInt_mul (a b : Int64) : (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ 64) := by
  rw [← toInt_toBitVec, Int64.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem ISize.toInt_mul (a b : ISize) : (a * b).toInt = (a.toInt * b.toInt).bmod (2 ^ System.Platform.numBits) := by
  rw [← toInt_toBitVec, ISize.toBitVec_mul, BitVec.toInt_mul, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem Int16.toInt8_mul (a b : Int16) : (a * b).toInt8 = a.toInt8 * b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem Int32.toInt8_mul (a b : Int32) : (a * b).toInt8 = a.toInt8 * b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem Int32.toInt16_mul (a b : Int32) : (a * b).toInt16 = a.toInt16 * b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem ISize.toInt8_mul (a b : ISize) : (a * b).toInt8 = a.toInt8 * b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem ISize.toInt16_mul (a b : ISize) : (a * b).toInt16 = a.toInt16 * b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem ISize.toInt32_mul (a b : ISize) : (a * b).toInt32 = a.toInt32 * b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

@[simp] theorem Int64.toInt8_mul (a b : Int64) : (a * b).toInt8 = a.toInt8 * b.toInt8 :=
  Int8.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem Int64.toInt16_mul (a b : Int64) : (a * b).toInt16 = a.toInt16 * b.toInt16 :=
  Int16.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem Int64.toInt32_mul (a b : Int64) : (a * b).toInt32 = a.toInt32 * b.toInt32 :=
  Int32.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])
@[simp] theorem Int64.toISize_mul (a b : Int64) : (a * b).toISize = a.toISize * b.toISize :=
  ISize.toBitVec_inj.1 (by simp [BitVec.signExtend_eq_setWidth_of_le, BitVec.setWidth_mul])

protected theorem Int8.sub_eq_add_neg (a b : Int8) : a - b = a + -b := Int8.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])
protected theorem Int16.sub_eq_add_neg (a b : Int16) : a - b = a + -b := Int16.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])
protected theorem Int32.sub_eq_add_neg (a b : Int32) : a - b = a + -b := Int32.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])
protected theorem Int64.sub_eq_add_neg (a b : Int64) : a - b = a + -b := Int64.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])
protected theorem ISize.sub_eq_add_neg (a b : ISize) : a - b = a + -b := ISize.toBitVec.inj (by simp [BitVec.sub_eq_add_neg])

@[simp] theorem Int8.toInt_sub (a b : Int8) : (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ 8) := by
  simp [Int8.sub_eq_add_neg, Int.sub_eq_add_neg]
@[simp] theorem Int16.toInt_sub (a b : Int16) : (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ 16) := by
  simp [Int16.sub_eq_add_neg, Int.sub_eq_add_neg]
@[simp] theorem Int32.toInt_sub (a b : Int32) : (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ 32) := by
  simp [Int32.sub_eq_add_neg, Int.sub_eq_add_neg]
@[simp] theorem Int64.toInt_sub (a b : Int64) : (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ 64) := by
  simp [Int64.sub_eq_add_neg, Int.sub_eq_add_neg]
@[simp] theorem ISize.toInt_sub (a b : ISize) : (a - b).toInt = (a.toInt - b.toInt).bmod (2 ^ System.Platform.numBits) := by
  simp [ISize.sub_eq_add_neg, Int.sub_eq_add_neg, toInt_neg]

@[simp] theorem Int16.toInt8_sub (a b : Int16) : (a - b).toInt8 = a.toInt8 - b.toInt8 := by
  simp [Int16.sub_eq_add_neg, Int8.sub_eq_add_neg]

@[simp] theorem Int32.toInt8_sub (a b : Int32) : (a - b).toInt8 = a.toInt8 - b.toInt8 := by
  simp [Int32.sub_eq_add_neg, Int8.sub_eq_add_neg]
@[simp] theorem Int32.toInt16_sub (a b : Int32) : (a - b).toInt16 = a.toInt16 - b.toInt16 := by
  simp [Int32.sub_eq_add_neg, Int16.sub_eq_add_neg]

@[simp] theorem ISize.toInt8_sub (a b : ISize) : (a - b).toInt8 = a.toInt8 - b.toInt8 := by
  simp [ISize.sub_eq_add_neg, Int8.sub_eq_add_neg]
@[simp] theorem ISize.toInt16_sub (a b : ISize) : (a - b).toInt16 = a.toInt16 - b.toInt16 := by
  simp [ISize.sub_eq_add_neg, Int16.sub_eq_add_neg]
@[simp] theorem ISize.toInt32_sub (a b : ISize) : (a - b).toInt32 = a.toInt32 - b.toInt32 := by
  simp [ISize.sub_eq_add_neg, Int32.sub_eq_add_neg]

@[simp] theorem Int64.toInt8_sub (a b : Int64) : (a - b).toInt8 = a.toInt8 - b.toInt8 := by
  simp [Int64.sub_eq_add_neg, Int8.sub_eq_add_neg]
@[simp] theorem Int64.toInt16_sub (a b : Int64) : (a - b).toInt16 = a.toInt16 - b.toInt16 := by
  simp [Int64.sub_eq_add_neg, Int16.sub_eq_add_neg]
@[simp] theorem Int64.toInt32_sub (a b : Int64) : (a - b).toInt32 = a.toInt32 - b.toInt32 := by
  simp [Int64.sub_eq_add_neg, Int32.sub_eq_add_neg]
@[simp] theorem Int64.toISize_sub (a b : Int64) : (a - b).toISize = a.toISize - b.toISize := by
  simp [Int64.sub_eq_add_neg, ISize.sub_eq_add_neg]

@[simp] theorem Int8.toInt16_lt {a b : Int8} : a.toInt16 < b.toInt16 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int16.lt_iff_toInt_lt]
@[simp] theorem Int8.toInt32_lt {a b : Int8} : a.toInt32 < b.toInt32 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int32.lt_iff_toInt_lt]
@[simp] theorem Int8.toInt64_lt {a b : Int8} : a.toInt64 < b.toInt64 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int64.lt_iff_toInt_lt]
@[simp] theorem Int8.toISize_lt {a b : Int8} : a.toISize < b.toISize ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize.lt_iff_toInt_lt]

@[simp] theorem Int16.toInt32_lt {a b : Int16} : a.toInt32 < b.toInt32 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int32.lt_iff_toInt_lt]
@[simp] theorem Int16.toInt64_lt {a b : Int16} : a.toInt64 < b.toInt64 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int64.lt_iff_toInt_lt]
@[simp] theorem Int16.toISize_lt {a b : Int16} : a.toISize < b.toISize ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize.lt_iff_toInt_lt]

@[simp] theorem Int32.toInt64_lt {a b : Int32} : a.toInt64 < b.toInt64 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int64.lt_iff_toInt_lt]
@[simp] theorem Int32.toISize_lt {a b : Int32} : a.toISize < b.toISize ↔ a < b := by
  simp [lt_iff_toInt_lt, ISize.lt_iff_toInt_lt]

@[simp] theorem ISize.toInt64_lt {a b : ISize} : a.toInt64 < b.toInt64 ↔ a < b := by
  simp [lt_iff_toInt_lt, Int64.lt_iff_toInt_lt]

@[simp] theorem Int8.toInt16_le {a b : Int8} : a.toInt16 ≤ b.toInt16 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int16.le_iff_toInt_le]
@[simp] theorem Int8.toInt32_le {a b : Int8} : a.toInt32 ≤ b.toInt32 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int32.le_iff_toInt_le]
@[simp] theorem Int8.toInt64_le {a b : Int8} : a.toInt64 ≤ b.toInt64 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int64.le_iff_toInt_le]
@[simp] theorem Int8.toISize_le {a b : Int8} : a.toISize ≤ b.toISize ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize.le_iff_toInt_le]

@[simp] theorem Int16.toInt32_le {a b : Int16} : a.toInt32 ≤ b.toInt32 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int32.le_iff_toInt_le]
@[simp] theorem Int16.toInt64_le {a b : Int16} : a.toInt64 ≤ b.toInt64 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int64.le_iff_toInt_le]
@[simp] theorem Int16.toISize_le {a b : Int16} : a.toISize ≤ b.toISize ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize.le_iff_toInt_le]

@[simp] theorem Int32.toInt64_le {a b : Int32} : a.toInt64 ≤ b.toInt64 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int64.le_iff_toInt_le]
@[simp] theorem Int32.toISize_le {a b : Int32} : a.toISize ≤ b.toISize ↔ a ≤ b := by
  simp [le_iff_toInt_le, ISize.le_iff_toInt_le]

@[simp] theorem ISize.toInt64_le {a b : ISize} : a.toInt64 ≤ b.toInt64 ↔ a ≤ b := by
  simp [le_iff_toInt_le, Int64.le_iff_toInt_le]

@[simp] theorem Int8.ofBitVec_neg (a : BitVec 8) : Int8.ofBitVec (-a) = -Int8.ofBitVec a := (rfl)
@[simp] theorem Int16.ofBitVec_neg (a : BitVec 16) : Int16.ofBitVec (-a) = -Int16.ofBitVec a := (rfl)
@[simp] theorem Int32.ofBitVec_neg (a : BitVec 32) : Int32.ofBitVec (-a) = -Int32.ofBitVec a := (rfl)
@[simp] theorem Int64.ofBitVec_neg (a : BitVec 64) : Int64.ofBitVec (-a) = -Int64.ofBitVec a := (rfl)
@[simp] theorem ISize.ofBitVec_neg (a : BitVec System.Platform.numBits) : ISize.ofBitVec (-a) = -ISize.ofBitVec a := (rfl)

@[simp] theorem Int8.ofInt_neg (a : Int) : Int8.ofInt (-a) = -Int8.ofInt a := Int8.toInt_inj.1 (by simp)
@[simp] theorem Int16.ofInt_neg (a : Int) : Int16.ofInt (-a) = -Int16.ofInt a := Int16.toInt_inj.1 (by simp)
@[simp] theorem Int32.ofInt_neg (a : Int) : Int32.ofInt (-a) = -Int32.ofInt a := Int32.toInt_inj.1 (by simp)
@[simp] theorem Int64.ofInt_neg (a : Int) : Int64.ofInt (-a) = -Int64.ofInt a := Int64.toInt_inj.1 (by simp)
@[simp] theorem ISize.ofInt_neg (a : Int) : ISize.ofInt (-a) = -ISize.ofInt a :=
  ISize.toInt_inj.1 (by simp [ISize.toInt_ofInt, toInt_neg])

theorem Int8.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : Int8) : Int8.ofInt a = b ↔ a.bmod (2 ^ 8) = b.toInt := by
  simp [← Int8.toInt_inj]
theorem Int16.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : Int16) : Int16.ofInt a = b ↔ a.bmod (2 ^ 16) = b.toInt := by
  simp [← Int16.toInt_inj]
theorem Int32.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : Int32) : Int32.ofInt a = b ↔ a.bmod (2 ^ 32) = b.toInt := by
  simp [← Int32.toInt_inj]
theorem Int64.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : Int64) : Int64.ofInt a = b ↔ a.bmod (2 ^ 64) = b.toInt := by
  simp [← Int64.toInt_inj]
theorem ISize.ofInt_eq_iff_bmod_eq_toInt (a : Int) (b : ISize) : ISize.ofInt a = b ↔ a.bmod (2 ^ System.Platform.numBits) = b.toInt := by
  simp [← ISize.toInt_inj, ISize.toInt_ofInt]

@[simp] theorem Int8.ofBitVec_add (a b : BitVec 8) : Int8.ofBitVec (a + b) = Int8.ofBitVec a + Int8.ofBitVec b := (rfl)
@[simp] theorem Int16.ofBitVec_add (a b : BitVec 16) : Int16.ofBitVec (a + b) = Int16.ofBitVec a + Int16.ofBitVec b := (rfl)
@[simp] theorem Int32.ofBitVec_add (a b : BitVec 32) : Int32.ofBitVec (a + b) = Int32.ofBitVec a + Int32.ofBitVec b := (rfl)
@[simp] theorem Int64.ofBitVec_add (a b : BitVec 64) : Int64.ofBitVec (a + b) = Int64.ofBitVec a + Int64.ofBitVec b := (rfl)
@[simp] theorem ISize.ofBitVec_add (a b : BitVec System.Platform.numBits) : ISize.ofBitVec (a + b) = ISize.ofBitVec a + ISize.ofBitVec b := (rfl)

@[simp] theorem Int8.ofInt_add (a b : Int) : Int8.ofInt (a + b) = Int8.ofInt a + Int8.ofInt b := by
  simp [Int8.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int16.ofInt_add (a b : Int) : Int16.ofInt (a + b) = Int16.ofInt a + Int16.ofInt b := by
  simp [Int16.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int32.ofInt_add (a b : Int) : Int32.ofInt (a + b) = Int32.ofInt a + Int32.ofInt b := by
  simp [Int32.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int64.ofInt_add (a b : Int) : Int64.ofInt (a + b) = Int64.ofInt a + Int64.ofInt b := by
  simp [Int64.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem ISize.ofInt_add (a b : Int) : ISize.ofInt (a + b) = ISize.ofInt a + ISize.ofInt b := by
  simp [ISize.ofInt_eq_iff_bmod_eq_toInt, ISize.toInt_ofInt]

@[simp] theorem Int8.ofNat_add (a b : Nat) : Int8.ofNat (a + b) = Int8.ofNat a + Int8.ofNat b := by
  simp [← Int8.ofInt_eq_ofNat]
@[simp] theorem Int16.ofNat_add (a b : Nat) : Int16.ofNat (a + b) = Int16.ofNat a + Int16.ofNat b := by
  simp [← Int16.ofInt_eq_ofNat]
@[simp] theorem Int32.ofNat_add (a b : Nat) : Int32.ofNat (a + b) = Int32.ofNat a + Int32.ofNat b := by
  simp [← Int32.ofInt_eq_ofNat]
@[simp] theorem Int64.ofNat_add (a b : Nat) : Int64.ofNat (a + b) = Int64.ofNat a + Int64.ofNat b := by
  simp [← Int64.ofInt_eq_ofNat]
@[simp] theorem ISize.ofNat_add (a b : Nat) : ISize.ofNat (a + b) = ISize.ofNat a + ISize.ofNat b := by
  simp [← ISize.ofInt_eq_ofNat]

theorem Int8.ofIntLE_add {a b : Int} {hab₁ hab₂} : Int8.ofIntLE (a + b) hab₁ hab₂ = Int8.ofInt a + Int8.ofInt b := by
  simp [Int8.ofIntLE_eq_ofInt]
theorem Int16.ofIntLE_add {a b : Int} {hab₁ hab₂} : Int16.ofIntLE (a + b) hab₁ hab₂ = Int16.ofInt a + Int16.ofInt b := by
  simp [Int16.ofIntLE_eq_ofInt]
theorem Int32.ofIntLE_add {a b : Int} {hab₁ hab₂} : Int32.ofIntLE (a + b) hab₁ hab₂ = Int32.ofInt a + Int32.ofInt b := by
  simp [Int32.ofIntLE_eq_ofInt]
theorem Int64.ofIntLE_add {a b : Int} {hab₁ hab₂} : Int64.ofIntLE (a + b) hab₁ hab₂ = Int64.ofInt a + Int64.ofInt b := by
  simp [Int64.ofIntLE_eq_ofInt]
theorem ISize.ofIntLE_add {a b : Int} {hab₁ hab₂} : ISize.ofIntLE (a + b) hab₁ hab₂ = ISize.ofInt a + ISize.ofInt b := by
  simp [ISize.ofIntLE_eq_ofInt]

@[simp] theorem Int8.ofBitVec_sub (a b : BitVec 8) : Int8.ofBitVec (a - b) = Int8.ofBitVec a - Int8.ofBitVec b := (rfl)
@[simp] theorem Int16.ofBitVec_sub (a b : BitVec 16) : Int16.ofBitVec (a - b) = Int16.ofBitVec a - Int16.ofBitVec b := (rfl)
@[simp] theorem Int32.ofBitVec_sub (a b : BitVec 32) : Int32.ofBitVec (a - b) = Int32.ofBitVec a - Int32.ofBitVec b := (rfl)
@[simp] theorem Int64.ofBitVec_sub (a b : BitVec 64) : Int64.ofBitVec (a - b) = Int64.ofBitVec a - Int64.ofBitVec b := (rfl)
@[simp] theorem ISize.ofBitVec_sub (a b : BitVec System.Platform.numBits) : ISize.ofBitVec (a - b) = ISize.ofBitVec a - ISize.ofBitVec b := (rfl)

@[simp] theorem Int8.ofInt_sub (a b : Int) : Int8.ofInt (a - b) = Int8.ofInt a - Int8.ofInt b := by
  simp [Int8.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int16.ofInt_sub (a b : Int) : Int16.ofInt (a - b) = Int16.ofInt a - Int16.ofInt b := by
  simp [Int16.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int32.ofInt_sub (a b : Int) : Int32.ofInt (a - b) = Int32.ofInt a - Int32.ofInt b := by
  simp [Int32.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int64.ofInt_sub (a b : Int) : Int64.ofInt (a - b) = Int64.ofInt a - Int64.ofInt b := by
  simp [Int64.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem ISize.ofInt_sub (a b : Int) : ISize.ofInt (a - b) = ISize.ofInt a - ISize.ofInt b := by
  simp [ISize.ofInt_eq_iff_bmod_eq_toInt, ISize.toInt_ofInt]

@[simp] theorem Int8.ofNat_sub (a b : Nat) (hab : b ≤ a) : Int8.ofNat (a - b) = Int8.ofNat a - Int8.ofNat b := by
  simp [← Int8.ofInt_eq_ofNat, Int.ofNat_sub hab]
@[simp] theorem Int16.ofNat_sub (a b : Nat) (hab : b ≤ a) : Int16.ofNat (a - b) = Int16.ofNat a - Int16.ofNat b := by
  simp [← Int16.ofInt_eq_ofNat, Int.ofNat_sub hab]
@[simp] theorem Int32.ofNat_sub (a b : Nat) (hab : b ≤ a) : Int32.ofNat (a - b) = Int32.ofNat a - Int32.ofNat b := by
  simp [← Int32.ofInt_eq_ofNat, Int.ofNat_sub hab]
@[simp] theorem Int64.ofNat_sub (a b : Nat) (hab : b ≤ a) : Int64.ofNat (a - b) = Int64.ofNat a - Int64.ofNat b := by
  simp [← Int64.ofInt_eq_ofNat, Int.ofNat_sub hab]
@[simp] theorem ISize.ofNat_sub (a b : Nat) (hab : b ≤ a) : ISize.ofNat (a - b) = ISize.ofNat a - ISize.ofNat b := by
  simp [← ISize.ofInt_eq_ofNat, Int.ofNat_sub hab]

theorem Int8.ofIntLE_sub {a b : Int} {hab₁ hab₂} : Int8.ofIntLE (a - b) hab₁ hab₂ = Int8.ofInt a - Int8.ofInt b := by
  simp [Int8.ofIntLE_eq_ofInt]
theorem Int16.ofIntLE_sub {a b : Int} {hab₁ hab₂} : Int16.ofIntLE (a - b) hab₁ hab₂ = Int16.ofInt a - Int16.ofInt b := by
  simp [Int16.ofIntLE_eq_ofInt]
theorem Int32.ofIntLE_sub {a b : Int} {hab₁ hab₂} : Int32.ofIntLE (a - b) hab₁ hab₂ = Int32.ofInt a - Int32.ofInt b := by
  simp [Int32.ofIntLE_eq_ofInt]
theorem Int64.ofIntLE_sub {a b : Int} {hab₁ hab₂} : Int64.ofIntLE (a - b) hab₁ hab₂ = Int64.ofInt a - Int64.ofInt b := by
  simp [Int64.ofIntLE_eq_ofInt]
theorem ISize.ofIntLE_sub {a b : Int} {hab₁ hab₂} : ISize.ofIntLE (a - b) hab₁ hab₂ = ISize.ofInt a - ISize.ofInt b := by
  simp [ISize.ofIntLE_eq_ofInt]

@[simp] theorem Int8.ofBitVec_mul (a b : BitVec 8) : Int8.ofBitVec (a * b) = Int8.ofBitVec a * Int8.ofBitVec b := (rfl)
@[simp] theorem Int16.ofBitVec_mul (a b : BitVec 16) : Int16.ofBitVec (a * b) = Int16.ofBitVec a * Int16.ofBitVec b := (rfl)
@[simp] theorem Int32.ofBitVec_mul (a b : BitVec 32) : Int32.ofBitVec (a * b) = Int32.ofBitVec a * Int32.ofBitVec b := (rfl)
@[simp] theorem Int64.ofBitVec_mul (a b : BitVec 64) : Int64.ofBitVec (a * b) = Int64.ofBitVec a * Int64.ofBitVec b := (rfl)
@[simp] theorem ISize.ofBitVec_mul (a b : BitVec System.Platform.numBits) : ISize.ofBitVec (a * b) = ISize.ofBitVec a * ISize.ofBitVec b := (rfl)

@[simp] theorem Int8.ofInt_mul (a b : Int) : Int8.ofInt (a * b) = Int8.ofInt a * Int8.ofInt b := by
  simp [Int8.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int16.ofInt_mul (a b : Int) : Int16.ofInt (a * b) = Int16.ofInt a * Int16.ofInt b := by
  simp [Int16.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int32.ofInt_mul (a b : Int) : Int32.ofInt (a * b) = Int32.ofInt a * Int32.ofInt b := by
  simp [Int32.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem Int64.ofInt_mul (a b : Int) : Int64.ofInt (a * b) = Int64.ofInt a * Int64.ofInt b := by
  simp [Int64.ofInt_eq_iff_bmod_eq_toInt]
@[simp] theorem ISize.ofInt_mul (a b : Int) : ISize.ofInt (a * b) = ISize.ofInt a * ISize.ofInt b := by
  simp [ISize.ofInt_eq_iff_bmod_eq_toInt, ISize.toInt_ofInt]

@[simp] theorem Int8.ofNat_mul (a b : Nat) : Int8.ofNat (a * b) = Int8.ofNat a * Int8.ofNat b := by
  simp [← Int8.ofInt_eq_ofNat]
@[simp] theorem Int16.ofNat_mul (a b : Nat) : Int16.ofNat (a * b) = Int16.ofNat a * Int16.ofNat b := by
  simp [← Int16.ofInt_eq_ofNat]
@[simp] theorem Int32.ofNat_mul (a b : Nat) : Int32.ofNat (a * b) = Int32.ofNat a * Int32.ofNat b := by
  simp [← Int32.ofInt_eq_ofNat]
@[simp] theorem Int64.ofNat_mul (a b : Nat) : Int64.ofNat (a * b) = Int64.ofNat a * Int64.ofNat b := by
  simp [← Int64.ofInt_eq_ofNat]
@[simp] theorem ISize.ofNat_mul (a b : Nat) : ISize.ofNat (a * b) = ISize.ofNat a * ISize.ofNat b := by
  simp [← ISize.ofInt_eq_ofNat]

theorem Int8.ofIntLE_mul {a b : Int} {hab₁ hab₂} : Int8.ofIntLE (a * b) hab₁ hab₂ = Int8.ofInt a * Int8.ofInt b := by
  simp [Int8.ofIntLE_eq_ofInt]
theorem Int16.ofIntLE_mul {a b : Int} {hab₁ hab₂} : Int16.ofIntLE (a * b) hab₁ hab₂ = Int16.ofInt a * Int16.ofInt b := by
  simp [Int16.ofIntLE_eq_ofInt]
theorem Int32.ofIntLE_mul {a b : Int} {hab₁ hab₂} : Int32.ofIntLE (a * b) hab₁ hab₂ = Int32.ofInt a * Int32.ofInt b := by
  simp [Int32.ofIntLE_eq_ofInt]
theorem Int64.ofIntLE_mul {a b : Int} {hab₁ hab₂} : Int64.ofIntLE (a * b) hab₁ hab₂ = Int64.ofInt a * Int64.ofInt b := by
  simp [Int64.ofIntLE_eq_ofInt]
theorem ISize.ofIntLE_mul {a b : Int} {hab₁ hab₂} : ISize.ofIntLE (a * b) hab₁ hab₂ = ISize.ofInt a * ISize.ofInt b := by
  simp [ISize.ofIntLE_eq_ofInt]

theorem Int8.toInt_minValue_lt_zero : minValue.toInt < 0 := by decide
theorem Int16.toInt_minValue_lt_zero : minValue.toInt < 0 := by decide
theorem Int32.toInt_minValue_lt_zero : minValue.toInt < 0 := by decide
theorem Int64.toInt_minValue_lt_zero : minValue.toInt < 0 := by decide
theorem ISize.toInt_minValue_lt_zero : minValue.toInt < 0 := by
  rw [toInt_minValue, Int.neg_lt_zero_iff]
  exact Int.pow_pos (by decide)

theorem Int8.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ 7 := (rfl)
theorem Int16.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ 15 := (rfl)
theorem Int32.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ 31 := (rfl)
theorem Int64.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ 63 := (rfl)
theorem ISize.toInt_maxValue_add_one : maxValue.toInt + 1 = 2 ^ (System.Platform.numBits - 1) := by
  rw [toInt_maxValue, Int.sub_add_cancel]

@[simp] theorem Int8.ofBitVec_sdiv (a b : BitVec 8) : Int8.ofBitVec (a.sdiv b) = Int8.ofBitVec a / Int8.ofBitVec b := (rfl)
@[simp] theorem Int16.ofBitVec_sdiv (a b : BitVec 16) : Int16.ofBitVec (a.sdiv b) = Int16.ofBitVec a / Int16.ofBitVec b := (rfl)
@[simp] theorem Int32.ofBitVec_sdiv (a b : BitVec 32) : Int32.ofBitVec (a.sdiv b) = Int32.ofBitVec a / Int32.ofBitVec b := (rfl)
@[simp] theorem Int64.ofBitVec_sdiv (a b : BitVec 64) : Int64.ofBitVec (a.sdiv b) = Int64.ofBitVec a / Int64.ofBitVec b := (rfl)
@[simp] theorem ISize.ofBitVec_sdiv (a b : BitVec System.Platform.numBits) : ISize.ofBitVec (a.sdiv b) = ISize.ofBitVec a / ISize.ofBitVec b := (rfl)

theorem Int8.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int8.ofInt (a.tdiv b) = Int8.ofInt a / Int8.ofInt b := by
  rw [Int8.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem Int16.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int16.ofInt (a.tdiv b) = Int16.ofInt a / Int16.ofInt b := by
  rw [Int16.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem Int32.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int32.ofInt (a.tdiv b) = Int32.ofInt a / Int32.ofInt b := by
  rw [Int32.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem Int64.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int64.ofInt (a.tdiv b) = Int64.ofInt a / Int64.ofInt b := by
  rw [Int64.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem ISize.ofInt_tdiv {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize.ofInt (a.tdiv b) = ISize.ofInt a / ISize.ofInt b := by
  rw [ISize.ofInt_eq_iff_bmod_eq_toInt, toInt_div, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact le_of_eq_of_le (by cases System.Platform.numBits_eq <;> simp_all [size, toInt_ofInt, toInt_neg]) hb₁
  · refine Int.lt_of_le_sub_one (le_of_le_of_eq hb₂ ?_)
    cases System.Platform.numBits_eq <;> simp_all [size, toInt_ofInt]
  · exact le_of_eq_of_le (by cases System.Platform.numBits_eq <;> simp_all [size, toInt_ofInt, toInt_neg]) ha₁
  · refine Int.lt_of_le_sub_one (le_of_le_of_eq ha₂ ?_)
    cases System.Platform.numBits_eq <;> simp_all [size, toInt_ofInt]

theorem Int8.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int8.ofInt (a.tdiv b) = Int8.ofIntLE a ha₁ ha₂ / Int8.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]
theorem Int16.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int16.ofInt (a.tdiv b) = Int16.ofIntLE a ha₁ ha₂ / Int16.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]
theorem Int32.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int32.ofInt (a.tdiv b) = Int32.ofIntLE a ha₁ ha₂ / Int32.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]
theorem Int64.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int64.ofInt (a.tdiv b) = Int64.ofIntLE a ha₁ ha₂ / Int64.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]
theorem ISize.ofInt_eq_ofIntLE_div {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize.ofInt (a.tdiv b) = ISize.ofIntLE a ha₁ ha₂ / ISize.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tdiv ha₁ ha₂ hb₁ hb₂]

theorem Int8.ofNat_div {a b : Nat} (ha : a < 2 ^ 7) (hb : b < 2 ^ 7) :
    Int8.ofNat (a / b) = Int8.ofNat a / Int8.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv,
    ofInt_tdiv (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int16.ofNat_div {a b : Nat} (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) :
    Int16.ofNat (a / b) = Int16.ofNat a / Int16.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv,
    ofInt_tdiv (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int32.ofNat_div {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    Int32.ofNat (a / b) = Int32.ofNat a / Int32.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv,
    ofInt_tdiv (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int64.ofNat_div {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Int64.ofNat (a / b) = Int64.ofNat a / Int64.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv,
    ofInt_tdiv (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem ISize.ofNat_div {a b : Nat} (ha : a < 2 ^ (System.Platform.numBits - 1)) (hb : b < 2 ^ (System.Platform.numBits - 1)) :
    ISize.ofNat (a / b) = ISize.ofNat a / ISize.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tdiv, ofInt_tdiv]
  · exact Int.le_of_lt (Int.lt_of_lt_of_le ISize.toInt_minValue_lt_zero (Int.ofNat_zero_le _))
  · apply Int.le_of_lt_add_one
    simpa only [toInt_maxValue_add_one, ← Int.ofNat_lt, Int.natCast_pow] using ha
  · exact Int.le_of_lt (Int.lt_of_lt_of_le ISize.toInt_minValue_lt_zero (Int.ofNat_zero_le _))
  · apply Int.le_of_lt_add_one
    simpa only [toInt_maxValue_add_one, ← Int.ofNat_lt, Int.natCast_pow] using hb

@[simp] theorem Int8.ofBitVec_srem (a b : BitVec 8) : Int8.ofBitVec (a.srem b) = Int8.ofBitVec a % Int8.ofBitVec b := (rfl)
@[simp] theorem Int16.ofBitVec_srem (a b : BitVec 16) : Int16.ofBitVec (a.srem b) = Int16.ofBitVec a % Int16.ofBitVec b := (rfl)
@[simp] theorem Int32.ofBitVec_srem (a b : BitVec 32) : Int32.ofBitVec (a.srem b) = Int32.ofBitVec a % Int32.ofBitVec b := (rfl)
@[simp] theorem Int64.ofBitVec_srem (a b : BitVec 64) : Int64.ofBitVec (a.srem b) = Int64.ofBitVec a % Int64.ofBitVec b := (rfl)
@[simp] theorem ISize.ofBitVec_srem (a b : BitVec System.Platform.numBits) : ISize.ofBitVec (a.srem b) = ISize.ofBitVec a % ISize.ofBitVec b := (rfl)

@[simp] theorem Int8.toInt_bmod_size (a : Int8) : a.toInt.bmod size = a.toInt := BitVec.toInt_bmod_cancel _
@[simp] theorem Int16.toInt_bmod_size (a : Int16) : a.toInt.bmod size = a.toInt := BitVec.toInt_bmod_cancel _
@[simp] theorem Int32.toInt_bmod_size (a : Int32) : a.toInt.bmod size = a.toInt := BitVec.toInt_bmod_cancel _
@[simp] theorem Int64.toInt_bmod_size (a : Int64) : a.toInt.bmod size = a.toInt := BitVec.toInt_bmod_cancel _
@[simp] theorem ISize.toInt_bmod_size (a : ISize) : a.toInt.bmod size = a.toInt := BitVec.toInt_bmod_cancel _

theorem Int8.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int8.ofIntLE a ha₁ ha₂ ≤ Int8.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by simp [le_iff_toInt_le]
theorem Int16.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int16.ofIntLE a ha₁ ha₂ ≤ Int16.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by simp [le_iff_toInt_le]
theorem Int32.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int32.ofIntLE a ha₁ ha₂ ≤ Int32.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by simp [le_iff_toInt_le]
theorem Int64.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int64.ofIntLE a ha₁ ha₂ ≤ Int64.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by simp [le_iff_toInt_le]
theorem ISize.ofIntLE_le_iff_le {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize.ofIntLE a ha₁ ha₂ ≤ ISize.ofIntLE b hb₁ hb₂ ↔ a ≤ b := by simp [le_iff_toInt_le]

theorem Int8.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int8.ofInt a ≤ Int8.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]
theorem Int16.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int16.ofInt a ≤ Int16.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]
theorem Int32.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int32.ofInt a ≤ Int32.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]
theorem Int64.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int64.ofInt a ≤ Int64.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]
theorem ISize.ofInt_le_iff_le {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize.ofInt a ≤ ISize.ofInt b ↔ a ≤ b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_le_iff_le]

theorem Int8.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ 7) (hb : b < 2 ^ 7) :
    Int8.ofNat a ≤ Int8.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_le_iff_le (by simp) _ (by simp), Int.ofNat_le]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int16.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) :
    Int16.ofNat a ≤ Int16.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_le_iff_le (by simp) _ (by simp), Int.ofNat_le]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int32.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    Int32.ofNat a ≤ Int32.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_le_iff_le (by simp) _ (by simp), Int.ofNat_le]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int64.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Int64.ofNat a ≤ Int64.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_le_iff_le (by simp) _ (by simp), Int.ofNat_le]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem ISize.ofNat_le_iff_le {a b : Nat} (ha : a < 2 ^ (System.Platform.numBits - 1)) (hb : b < 2 ^ (System.Platform.numBits - 1)) :
    ISize.ofNat a ≤ ISize.ofNat b ↔ a ≤ b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_le_iff_le, Int.ofNat_le]
  · exact Int.le_of_lt (Int.lt_of_lt_of_le ISize.toInt_minValue_lt_zero (Int.ofNat_zero_le _))
  · apply Int.le_of_lt_add_one
    simpa only [toInt_maxValue_add_one, ← Int.ofNat_lt, Int.natCast_pow] using ha
  · exact Int.le_of_lt (Int.lt_of_lt_of_le ISize.toInt_minValue_lt_zero (Int.ofNat_zero_le _))
  · apply Int.le_of_lt_add_one
    simpa only [toInt_maxValue_add_one, ← Int.ofNat_lt, Int.natCast_pow] using hb

theorem Int8.ofBitVec_le_iff_sle (a b : BitVec 8) : Int8.ofBitVec a ≤ Int8.ofBitVec b ↔ a.sle b := Iff.rfl
theorem Int16.ofBitVec_le_iff_sle (a b : BitVec 16) : Int16.ofBitVec a ≤ Int16.ofBitVec b ↔ a.sle b := Iff.rfl
theorem Int32.ofBitVec_le_iff_sle (a b : BitVec 32) : Int32.ofBitVec a ≤ Int32.ofBitVec b ↔ a.sle b := Iff.rfl
theorem Int64.ofBitVec_le_iff_sle (a b : BitVec 64) : Int64.ofBitVec a ≤ Int64.ofBitVec b ↔ a.sle b := Iff.rfl
theorem ISize.ofBitVec_le_iff_sle (a b : BitVec System.Platform.numBits) : ISize.ofBitVec a ≤ ISize.ofBitVec b ↔ a.sle b := Iff.rfl

theorem Int8.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int8.ofIntLE a ha₁ ha₂ < Int8.ofIntLE b hb₁ hb₂ ↔ a < b := by simp [lt_iff_toInt_lt]
theorem Int16.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int16.ofIntLE a ha₁ ha₂ < Int16.ofIntLE b hb₁ hb₂ ↔ a < b := by simp [lt_iff_toInt_lt]
theorem Int32.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int32.ofIntLE a ha₁ ha₂ < Int32.ofIntLE b hb₁ hb₂ ↔ a < b := by simp [lt_iff_toInt_lt]
theorem Int64.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int64.ofIntLE a ha₁ ha₂ < Int64.ofIntLE b hb₁ hb₂ ↔ a < b := by simp [lt_iff_toInt_lt]
theorem ISize.ofIntLE_lt_iff_lt {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize.ofIntLE a ha₁ ha₂ < ISize.ofIntLE b hb₁ hb₂ ↔ a < b := by simp [lt_iff_toInt_lt]

theorem Int8.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int8.ofInt a < Int8.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]
theorem Int16.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int16.ofInt a < Int16.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]
theorem Int32.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int32.ofInt a < Int32.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]
theorem Int64.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int64.ofInt a < Int64.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]
theorem ISize.ofInt_lt_iff_lt {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize.ofInt a < ISize.ofInt b ↔ a < b := by
  rw [← ofIntLE_eq_ofInt ha₁ ha₂, ← ofIntLE_eq_ofInt hb₁ hb₂, ofIntLE_lt_iff_lt]

theorem Int8.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ 7) (hb : b < 2 ^ 7) :
    Int8.ofNat a < Int8.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_lt_iff_lt (by simp) _ (by simp), Int.ofNat_lt]
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 ha)
theorem Int16.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) :
    Int16.ofNat a < Int16.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_lt_iff_lt (by simp) _ (by simp), Int.ofNat_lt]
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 ha)
theorem Int32.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    Int32.ofNat a < Int32.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_lt_iff_lt (by simp) _ (by simp), Int.ofNat_lt]
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 ha)
theorem Int64.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Int64.ofNat a < Int64.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_lt_iff_lt (by simp) _ (by simp), Int.ofNat_lt]
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_lt.2 ha)
theorem ISize.ofNat_lt_iff_lt {a b : Nat} (ha : a < 2 ^ (System.Platform.numBits - 1)) (hb : b < 2 ^ (System.Platform.numBits - 1)) :
    ISize.ofNat a < ISize.ofNat b ↔ a < b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ofInt_lt_iff_lt, Int.ofNat_lt]
  · exact Int.le_of_lt (Int.lt_of_lt_of_le ISize.toInt_minValue_lt_zero (Int.ofNat_zero_le _))
  · apply Int.le_of_lt_add_one
    simpa only [toInt_maxValue_add_one, ← Int.ofNat_lt, Int.natCast_pow] using ha
  · exact Int.le_of_lt (Int.lt_of_lt_of_le ISize.toInt_minValue_lt_zero (Int.ofNat_zero_le _))
  · apply Int.le_of_lt_add_one
    simpa only [toInt_maxValue_add_one, ← Int.ofNat_lt, Int.natCast_pow] using hb

theorem Int8.ofBitVec_lt_iff_slt (a b : BitVec 8) : Int8.ofBitVec a < Int8.ofBitVec b ↔ a.slt b := Iff.rfl
theorem Int16.ofBitVec_lt_iff_slt (a b : BitVec 16) : Int16.ofBitVec a < Int16.ofBitVec b ↔ a.slt b := Iff.rfl
theorem Int32.ofBitVec_lt_iff_slt (a b : BitVec 32) : Int32.ofBitVec a < Int32.ofBitVec b ↔ a.slt b := Iff.rfl
theorem Int64.ofBitVec_lt_iff_slt (a b : BitVec 64) : Int64.ofBitVec a < Int64.ofBitVec b ↔ a.slt b := Iff.rfl
theorem ISize.ofBitVec_lt_iff_slt (a b : BitVec System.Platform.numBits) : ISize.ofBitVec a < ISize.ofBitVec b ↔ a.slt b := Iff.rfl

theorem Int8.toNatClampNeg_one : (1 : Int8).toNatClampNeg = 1 := (rfl)
theorem Int16.toNatClampNeg_one : (1 : Int16).toNatClampNeg = 1 := (rfl)
theorem Int32.toNatClampNeg_one : (1 : Int32).toNatClampNeg = 1 := (rfl)
theorem Int64.toNatClampNeg_one : (1 : Int64).toNatClampNeg = 1 := (rfl)
theorem ISize.toNatClampNeg_one : (1 : ISize).toNatClampNeg = 1 := by simp

theorem Int8.toInt_one : (1 : Int8).toInt = 1 := (rfl)
theorem Int16.toInt_one : (1 : Int16).toInt = 1 := (rfl)
theorem Int32.toInt_one : (1 : Int32).toInt = 1 := (rfl)
theorem Int64.toInt_one : (1 : Int64).toInt = 1 := (rfl)
theorem ISize.toInt_one : (1 : ISize).toInt = 1 := by simp

theorem Int8.zero_lt_one : (0 : Int8) < 1 := by simp
theorem Int16.zero_lt_one : (0 : Int16) < 1 := by simp
theorem Int32.zero_lt_one : (0 : Int32) < 1 := by simp
theorem Int64.zero_lt_one : (0 : Int64) < 1 := by simp
theorem ISize.zero_lt_one : (0 : ISize) < 1 := by simp [lt_iff_toInt_lt]

theorem Int8.zero_ne_one : (0 : Int8) ≠ 1 := by simp
theorem Int16.zero_ne_one : (0 : Int16) ≠ 1 := by simp
theorem Int32.zero_ne_one : (0 : Int32) ≠ 1 := by simp
theorem Int64.zero_ne_one : (0 : Int64) ≠ 1 := by simp
theorem ISize.zero_ne_one : (0 : ISize) ≠ 1 := by simp [← ISize.toInt_inj]

protected theorem Int8.add_assoc (a b c : Int8) : a + b + c = a + (b + c) :=
  Int8.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
protected theorem Int16.add_assoc (a b c : Int16) : a + b + c = a + (b + c) :=
  Int16.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
protected theorem Int32.add_assoc (a b c : Int32) : a + b + c = a + (b + c) :=
  Int32.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
protected theorem Int64.add_assoc (a b c : Int64) : a + b + c = a + (b + c) :=
  Int64.toBitVec_inj.1 (BitVec.add_assoc _ _ _)
protected theorem ISize.add_assoc (a b c : ISize) : a + b + c = a + (b + c) :=
  ISize.toBitVec_inj.1 (BitVec.add_assoc _ _ _)

instance : Std.Associative (α := Int8) (· + ·) := ⟨Int8.add_assoc⟩
instance : Std.Associative (α := Int16) (· + ·) := ⟨Int16.add_assoc⟩
instance : Std.Associative (α := Int32) (· + ·) := ⟨Int32.add_assoc⟩
instance : Std.Associative (α := Int64) (· + ·) := ⟨Int64.add_assoc⟩
instance : Std.Associative (α := ISize) (· + ·) := ⟨ISize.add_assoc⟩

protected theorem Int8.add_comm (a b : Int8) : a + b = b + a := Int8.toBitVec_inj.1 (BitVec.add_comm _ _)
protected theorem Int16.add_comm (a b : Int16) : a + b = b + a := Int16.toBitVec_inj.1 (BitVec.add_comm _ _)
protected theorem Int32.add_comm (a b : Int32) : a + b = b + a := Int32.toBitVec_inj.1 (BitVec.add_comm _ _)
protected theorem Int64.add_comm (a b : Int64) : a + b = b + a := Int64.toBitVec_inj.1 (BitVec.add_comm _ _)
protected theorem ISize.add_comm (a b : ISize) : a + b = b + a := ISize.toBitVec_inj.1 (BitVec.add_comm _ _)

instance : Std.Commutative (α := Int8) (· + ·) := ⟨Int8.add_comm⟩
instance : Std.Commutative (α := Int16) (· + ·) := ⟨Int16.add_comm⟩
instance : Std.Commutative (α := Int32) (· + ·) := ⟨Int32.add_comm⟩
instance : Std.Commutative (α := Int64) (· + ·) := ⟨Int64.add_comm⟩
instance : Std.Commutative (α := ISize) (· + ·) := ⟨ISize.add_comm⟩

@[simp] protected theorem Int8.add_zero (a : Int8) : a + 0 = a := Int8.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem Int16.add_zero (a : Int16) : a + 0 = a := Int16.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem Int32.add_zero (a : Int32) : a + 0 = a := Int32.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem Int64.add_zero (a : Int64) : a + 0 = a := Int64.toBitVec_inj.1 (BitVec.add_zero _)
@[simp] protected theorem ISize.add_zero (a : ISize) : a + 0 = a := ISize.toBitVec_inj.1 (BitVec.add_zero _)

@[simp] protected theorem Int8.zero_add (a : Int8) : 0 + a = a := Int8.toBitVec_inj.1 (BitVec.zero_add _)
@[simp] protected theorem Int16.zero_add (a : Int16) : 0 + a = a := Int16.toBitVec_inj.1 (BitVec.zero_add _)
@[simp] protected theorem Int32.zero_add (a : Int32) : 0 + a = a := Int32.toBitVec_inj.1 (BitVec.zero_add _)
@[simp] protected theorem Int64.zero_add (a : Int64) : 0 + a = a := Int64.toBitVec_inj.1 (BitVec.zero_add _)
@[simp] protected theorem ISize.zero_add (a : ISize) : 0 + a = a := ISize.toBitVec_inj.1 (BitVec.zero_add _)

instance : Std.LawfulIdentity (α := Int8) (· + ·) 0 where
  left_id := Int8.zero_add
  right_id := Int8.add_zero
instance : Std.LawfulIdentity (α := Int16) (· + ·) 0 where
  left_id := Int16.zero_add
  right_id := Int16.add_zero
instance : Std.LawfulIdentity (α := Int32) (· + ·) 0 where
  left_id := Int32.zero_add
  right_id := Int32.add_zero
instance : Std.LawfulIdentity (α := Int64) (· + ·) 0 where
  left_id := Int64.zero_add
  right_id := Int64.add_zero
instance : Std.LawfulIdentity (α := ISize) (· + ·) 0 where
  left_id := ISize.zero_add
  right_id := ISize.add_zero

@[simp] protected theorem Int8.sub_zero (a : Int8) : a - 0 = a := Int8.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem Int16.sub_zero (a : Int16) : a - 0 = a := Int16.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem Int32.sub_zero (a : Int32) : a - 0 = a := Int32.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem Int64.sub_zero (a : Int64) : a - 0 = a := Int64.toBitVec_inj.1 (BitVec.sub_zero _)
@[simp] protected theorem ISize.sub_zero (a : ISize) : a - 0 = a := ISize.toBitVec_inj.1 (BitVec.sub_zero _)

@[simp] protected theorem Int8.zero_sub (a : Int8) : 0 - a = -a := Int8.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem Int16.zero_sub (a : Int16) : 0 - a = -a := Int16.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem Int32.zero_sub (a : Int32) : 0 - a = -a := Int32.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem Int64.zero_sub (a : Int64) : 0 - a = -a := Int64.toBitVec_inj.1 (BitVec.zero_sub _)
@[simp] protected theorem ISize.zero_sub (a : ISize) : 0 - a = -a := ISize.toBitVec_inj.1 (BitVec.zero_sub _)

@[simp] protected theorem Int8.sub_self (a : Int8) : a - a = 0 := Int8.toBitVec_inj.1 (BitVec.sub_self _)
@[simp] protected theorem Int16.sub_self (a : Int16) : a - a = 0 := Int16.toBitVec_inj.1 (BitVec.sub_self _)
@[simp] protected theorem Int32.sub_self (a : Int32) : a - a = 0 := Int32.toBitVec_inj.1 (BitVec.sub_self _)
@[simp] protected theorem Int64.sub_self (a : Int64) : a - a = 0 := Int64.toBitVec_inj.1 (BitVec.sub_self _)
@[simp] protected theorem ISize.sub_self (a : ISize) : a - a = 0 := ISize.toBitVec_inj.1 (BitVec.sub_self _)

protected theorem Int8.add_left_neg (a : Int8) : -a + a = 0 := Int8.toBitVec_inj.1 (BitVec.add_left_neg _)
protected theorem Int8.add_right_neg (a : Int8) : a + -a = 0 := Int8.toBitVec_inj.1 (BitVec.add_right_neg _)
protected theorem Int16.add_left_neg (a : Int16) : -a + a = 0 := Int16.toBitVec_inj.1 (BitVec.add_left_neg _)
protected theorem Int16.add_right_neg (a : Int16) : a + -a = 0 := Int16.toBitVec_inj.1 (BitVec.add_right_neg _)
protected theorem Int32.add_left_neg (a : Int32) : -a + a = 0 := Int32.toBitVec_inj.1 (BitVec.add_left_neg _)
protected theorem Int32.add_right_neg (a : Int32) : a + -a = 0 := Int32.toBitVec_inj.1 (BitVec.add_right_neg _)
protected theorem Int64.add_left_neg (a : Int64) : -a + a = 0 := Int64.toBitVec_inj.1 (BitVec.add_left_neg _)
protected theorem Int64.add_right_neg (a : Int64) : a + -a = 0 := Int64.toBitVec_inj.1 (BitVec.add_right_neg _)
protected theorem ISize.add_left_neg (a : ISize) : -a + a = 0 := ISize.toBitVec_inj.1 (BitVec.add_left_neg _)
protected theorem ISize.add_right_neg (a : ISize) : a + -a = 0 := ISize.toBitVec_inj.1 (BitVec.add_right_neg _)

@[simp] protected theorem Int8.sub_add_cancel (a b : Int8) : a - b + b = a :=
  Int8.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
@[simp] protected theorem Int16.sub_add_cancel (a b : Int16) : a - b + b = a :=
  Int16.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
@[simp] protected theorem Int32.sub_add_cancel (a b : Int32) : a - b + b = a :=
  Int32.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
@[simp] protected theorem Int64.sub_add_cancel (a b : Int64) : a - b + b = a :=
  Int64.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)
@[simp] protected theorem ISize.sub_add_cancel (a b : ISize) : a - b + b = a :=
  ISize.toBitVec_inj.1 (BitVec.sub_add_cancel _ _)

protected theorem Int8.eq_sub_iff_add_eq {a b c : Int8} : a = c - b ↔ a + b = c := by
  simpa [← Int8.toBitVec_inj] using BitVec.eq_sub_iff_add_eq
protected theorem Int16.eq_sub_iff_add_eq {a b c : Int16} : a = c - b ↔ a + b = c := by
  simpa [← Int16.toBitVec_inj] using BitVec.eq_sub_iff_add_eq
protected theorem Int32.eq_sub_iff_add_eq {a b c : Int32} : a = c - b ↔ a + b = c := by
  simpa [← Int32.toBitVec_inj] using BitVec.eq_sub_iff_add_eq
protected theorem Int64.eq_sub_iff_add_eq {a b c : Int64} : a = c - b ↔ a + b = c := by
  simpa [← Int64.toBitVec_inj] using BitVec.eq_sub_iff_add_eq
protected theorem ISize.eq_sub_iff_add_eq {a b c : ISize} : a = c - b ↔ a + b = c := by
  simpa [← ISize.toBitVec_inj] using BitVec.eq_sub_iff_add_eq

protected theorem Int8.sub_eq_iff_eq_add {a b c : Int8} : a - b = c ↔ a = c + b := by
  simpa [← Int8.toBitVec_inj] using BitVec.sub_eq_iff_eq_add
protected theorem Int16.sub_eq_iff_eq_add {a b c : Int16} : a - b = c ↔ a = c + b := by
  simpa [← Int16.toBitVec_inj] using BitVec.sub_eq_iff_eq_add
protected theorem Int32.sub_eq_iff_eq_add {a b c : Int32} : a - b = c ↔ a = c + b := by
  simpa [← Int32.toBitVec_inj] using BitVec.sub_eq_iff_eq_add
protected theorem Int64.sub_eq_iff_eq_add {a b c : Int64} : a - b = c ↔ a = c + b := by
  simpa [← Int64.toBitVec_inj] using BitVec.sub_eq_iff_eq_add
protected theorem ISize.sub_eq_iff_eq_add {a b c : ISize} : a - b = c ↔ a = c + b := by
  simpa [← ISize.toBitVec_inj] using BitVec.sub_eq_iff_eq_add

@[simp] protected theorem Int8.neg_neg {a : Int8} : - -a = a := Int8.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem Int16.neg_neg {a : Int16} : - -a = a := Int16.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem Int32.neg_neg {a : Int32} : - -a = a := Int32.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem Int64.neg_neg {a : Int64} : - -a = a := Int64.toBitVec_inj.1 BitVec.neg_neg
@[simp] protected theorem ISize.neg_neg {a : ISize} : - -a = a := ISize.toBitVec_inj.1 BitVec.neg_neg

@[simp] protected theorem Int8.neg_inj {a b : Int8} : -a = -b ↔ a = b := by simp [← Int8.toBitVec_inj]
@[simp] protected theorem Int16.neg_inj {a b : Int16} : -a = -b ↔ a = b := by simp [← Int16.toBitVec_inj]
@[simp] protected theorem Int32.neg_inj {a b : Int32} : -a = -b ↔ a = b := by simp [← Int32.toBitVec_inj]
@[simp] protected theorem Int64.neg_inj {a b : Int64} : -a = -b ↔ a = b := by simp [← Int64.toBitVec_inj]
@[simp] protected theorem ISize.neg_inj {a b : ISize} : -a = -b ↔ a = b := by simp [← ISize.toBitVec_inj]

@[simp] protected theorem Int8.neg_ne_zero {a : Int8} : -a ≠ 0 ↔ a ≠ 0 := by simp [← Int8.toBitVec_inj]
@[simp] protected theorem Int16.neg_ne_zero {a : Int16} : -a ≠ 0 ↔ a ≠ 0 := by simp [← Int16.toBitVec_inj]
@[simp] protected theorem Int32.neg_ne_zero {a : Int32} : -a ≠ 0 ↔ a ≠ 0 := by simp [← Int32.toBitVec_inj]
@[simp] protected theorem Int64.neg_ne_zero {a : Int64} : -a ≠ 0 ↔ a ≠ 0 := by simp [← Int64.toBitVec_inj]
@[simp] protected theorem ISize.neg_ne_zero {a : ISize} : -a ≠ 0 ↔ a ≠ 0 := by simp [← ISize.toBitVec_inj]

protected theorem Int8.neg_add {a b : Int8} : - (a + b) = -a - b := Int8.toBitVec_inj.1 BitVec.neg_add
protected theorem Int16.neg_add {a b : Int16} : - (a + b) = -a - b := Int16.toBitVec_inj.1 BitVec.neg_add
protected theorem Int32.neg_add {a b : Int32} : - (a + b) = -a - b := Int32.toBitVec_inj.1 BitVec.neg_add
protected theorem Int64.neg_add {a b : Int64} : - (a + b) = -a - b := Int64.toBitVec_inj.1 BitVec.neg_add
protected theorem ISize.neg_add {a b : ISize} : - (a + b) = -a - b := ISize.toBitVec_inj.1 BitVec.neg_add

@[simp] protected theorem Int8.sub_neg {a b : Int8} : a - -b = a + b := Int8.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem Int16.sub_neg {a b : Int16} : a - -b = a + b := Int16.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem Int32.sub_neg {a b : Int32} : a - -b = a + b := Int32.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem Int64.sub_neg {a b : Int64} : a - -b = a + b := Int64.toBitVec_inj.1 BitVec.sub_neg
@[simp] protected theorem ISize.sub_neg {a b : ISize} : a - -b = a + b := ISize.toBitVec_inj.1 BitVec.sub_neg

@[simp] protected theorem Int8.neg_sub {a b : Int8} : -(a - b) = b - a := by
  rw [Int8.sub_eq_add_neg, Int8.neg_add, Int8.sub_neg, Int8.add_comm, ← Int8.sub_eq_add_neg]
@[simp] protected theorem Int16.neg_sub {a b : Int16} : -(a - b) = b - a := by
  rw [Int16.sub_eq_add_neg, Int16.neg_add, Int16.sub_neg, Int16.add_comm, ← Int16.sub_eq_add_neg]
@[simp] protected theorem Int32.neg_sub {a b : Int32} : -(a - b) = b - a := by
  rw [Int32.sub_eq_add_neg, Int32.neg_add, Int32.sub_neg, Int32.add_comm, ← Int32.sub_eq_add_neg]
@[simp] protected theorem Int64.neg_sub {a b : Int64} : -(a - b) = b - a := by
  rw [Int64.sub_eq_add_neg, Int64.neg_add, Int64.sub_neg, Int64.add_comm, ← Int64.sub_eq_add_neg]
@[simp] protected theorem ISize.neg_sub {a b : ISize} : -(a - b) = b - a := by
  rw [ISize.sub_eq_add_neg, ISize.neg_add, ISize.sub_neg, ISize.add_comm, ← ISize.sub_eq_add_neg]

@[simp] protected theorem Int8.add_left_inj {a b : Int8} (c : Int8) : (a + c = b + c) ↔ a = b := by
  simp [← Int8.toBitVec_inj]
@[simp] protected theorem Int16.add_left_inj {a b : Int16} (c : Int16) : (a + c = b + c) ↔ a = b := by
  simp [← Int16.toBitVec_inj]
@[simp] protected theorem Int32.add_left_inj {a b : Int32} (c : Int32) : (a + c = b + c) ↔ a = b := by
  simp [← Int32.toBitVec_inj]
@[simp] protected theorem Int64.add_left_inj {a b : Int64} (c : Int64) : (a + c = b + c) ↔ a = b := by
  simp [← Int64.toBitVec_inj]
@[simp] protected theorem ISize.add_left_inj {a b : ISize} (c : ISize) : (a + c = b + c) ↔ a = b := by
  simp [← ISize.toBitVec_inj]

@[simp] protected theorem Int8.add_right_inj {a b : Int8} (c : Int8) : (c + a = c + b) ↔ a = b := by
  simp [← Int8.toBitVec_inj]
@[simp] protected theorem Int16.add_right_inj {a b : Int16} (c : Int16) : (c + a = c + b) ↔ a = b := by
  simp [← Int16.toBitVec_inj]
@[simp] protected theorem Int32.add_right_inj {a b : Int32} (c : Int32) : (c + a = c + b) ↔ a = b := by
  simp [← Int32.toBitVec_inj]
@[simp] protected theorem Int64.add_right_inj {a b : Int64} (c : Int64) : (c + a = c + b) ↔ a = b := by
  simp [← Int64.toBitVec_inj]
@[simp] protected theorem ISize.add_right_inj {a b : ISize} (c : ISize) : (c + a = c + b) ↔ a = b := by
  simp [← ISize.toBitVec_inj]

@[simp] protected theorem Int8.sub_left_inj {a b : Int8} (c : Int8) : (a - c = b - c) ↔ a = b := by
  simp [← Int8.toBitVec_inj]
@[simp] protected theorem Int16.sub_left_inj {a b : Int16} (c : Int16) : (a - c = b - c) ↔ a = b := by
  simp [← Int16.toBitVec_inj]
@[simp] protected theorem Int32.sub_left_inj {a b : Int32} (c : Int32) : (a - c = b - c) ↔ a = b := by
  simp [← Int32.toBitVec_inj]
@[simp] protected theorem Int64.sub_left_inj {a b : Int64} (c : Int64) : (a - c = b - c) ↔ a = b := by
  simp [← Int64.toBitVec_inj]
@[simp] protected theorem ISize.sub_left_inj {a b : ISize} (c : ISize) : (a - c = b - c) ↔ a = b := by
  simp [← ISize.toBitVec_inj]

@[simp] protected theorem Int8.sub_right_inj {a b : Int8} (c : Int8) : (c - a = c - b) ↔ a = b := by
  simp [← Int8.toBitVec_inj]
@[simp] protected theorem Int16.sub_right_inj {a b : Int16} (c : Int16) : (c - a = c - b) ↔ a = b := by
  simp [← Int16.toBitVec_inj]
@[simp] protected theorem Int32.sub_right_inj {a b : Int32} (c : Int32) : (c - a = c - b) ↔ a = b := by
  simp [← Int32.toBitVec_inj]
@[simp] protected theorem Int64.sub_right_inj {a b : Int64} (c : Int64) : (c - a = c - b) ↔ a = b := by
  simp [← Int64.toBitVec_inj]
@[simp] protected theorem ISize.sub_right_inj {a b : ISize} (c : ISize) : (c - a = c - b) ↔ a = b := by
  simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.add_eq_right {a b : Int8} : a + b = b ↔ a = 0 := by
  simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.add_eq_right {a b : Int16} : a + b = b ↔ a = 0 := by
  simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.add_eq_right {a b : Int32} : a + b = b ↔ a = 0 := by
  simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.add_eq_right {a b : Int64} : a + b = b ↔ a = 0 := by
  simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.add_eq_right {a b : ISize} : a + b = b ↔ a = 0 := by
  simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.add_eq_left {a b : Int8} : a + b = a ↔ b = 0 := by
  simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.add_eq_left {a b : Int16} : a + b = a ↔ b = 0 := by
  simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.add_eq_left {a b : Int32} : a + b = a ↔ b = 0 := by
  simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.add_eq_left {a b : Int64} : a + b = a ↔ b = 0 := by
  simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.add_eq_left {a b : ISize} : a + b = a ↔ b = 0 := by
  simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.right_eq_add {a b : Int8} : b = a + b ↔ a = 0 := by
  simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.right_eq_add {a b : Int16} : b = a + b ↔ a = 0 := by
  simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.right_eq_add {a b : Int32} : b = a + b ↔ a = 0 := by
  simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.right_eq_add {a b : Int64} : b = a + b ↔ a = 0 := by
  simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.right_eq_add {a b : ISize} : b = a + b ↔ a = 0 := by
  simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.left_eq_add {a b : Int8} : a = a + b ↔ b = 0 := by
  simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.left_eq_add {a b : Int16} : a = a + b ↔ b = 0 := by
  simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.left_eq_add {a b : Int32} : a = a + b ↔ b = 0 := by
  simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.left_eq_add {a b : Int64} : a = a + b ↔ b = 0 := by
  simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.left_eq_add {a b : ISize} : a = a + b ↔ b = 0 := by
  simp [← ISize.toBitVec_inj]

protected theorem Int8.mul_comm (a b : Int8) : a * b = b * a := Int8.toBitVec_inj.1 (BitVec.mul_comm _ _)
protected theorem Int16.mul_comm (a b : Int16) : a * b = b * a := Int16.toBitVec_inj.1 (BitVec.mul_comm _ _)
protected theorem Int32.mul_comm (a b : Int32) : a * b = b * a := Int32.toBitVec_inj.1 (BitVec.mul_comm _ _)
protected theorem Int64.mul_comm (a b : Int64) : a * b = b * a := Int64.toBitVec_inj.1 (BitVec.mul_comm _ _)
protected theorem ISize.mul_comm (a b : ISize) : a * b = b * a := ISize.toBitVec_inj.1 (BitVec.mul_comm _ _)

instance : Std.Commutative (α := Int8) (· * ·) := ⟨Int8.mul_comm⟩
instance : Std.Commutative (α := Int16) (· * ·) := ⟨Int16.mul_comm⟩
instance : Std.Commutative (α := Int32) (· * ·) := ⟨Int32.mul_comm⟩
instance : Std.Commutative (α := Int64) (· * ·) := ⟨Int64.mul_comm⟩
instance : Std.Commutative (α := ISize) (· * ·) := ⟨ISize.mul_comm⟩

protected theorem Int8.mul_assoc (a b c : Int8) : a * b * c = a * (b * c) := Int8.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
protected theorem Int16.mul_assoc (a b c : Int16) : a * b * c = a * (b * c) := Int16.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
protected theorem Int32.mul_assoc (a b c : Int32) : a * b * c = a * (b * c) := Int32.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
protected theorem Int64.mul_assoc (a b c : Int64) : a * b * c = a * (b * c) := Int64.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)
protected theorem ISize.mul_assoc (a b c : ISize) : a * b * c = a * (b * c) := ISize.toBitVec_inj.1 (BitVec.mul_assoc _ _ _)

instance : Std.Associative (α := Int8) (· * ·) := ⟨Int8.mul_assoc⟩
instance : Std.Associative (α := Int16) (· * ·) := ⟨Int16.mul_assoc⟩
instance : Std.Associative (α := Int32) (· * ·) := ⟨Int32.mul_assoc⟩
instance : Std.Associative (α := Int64) (· * ·) := ⟨Int64.mul_assoc⟩
instance : Std.Associative (α := ISize) (· * ·) := ⟨ISize.mul_assoc⟩

@[simp] theorem Int8.mul_one (a : Int8) : a * 1 = a := Int8.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem Int16.mul_one (a : Int16) : a * 1 = a := Int16.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem Int32.mul_one (a : Int32) : a * 1 = a := Int32.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem Int64.mul_one (a : Int64) : a * 1 = a := Int64.toBitVec_inj.1 (BitVec.mul_one _)
@[simp] theorem ISize.mul_one (a : ISize) : a * 1 = a := ISize.toBitVec_inj.1 (BitVec.mul_one _)

@[simp] theorem Int8.one_mul (a : Int8) : 1 * a = a := Int8.toBitVec_inj.1 (BitVec.one_mul _)
@[simp] theorem Int16.one_mul (a : Int16) : 1 * a = a := Int16.toBitVec_inj.1 (BitVec.one_mul _)
@[simp] theorem Int32.one_mul (a : Int32) : 1 * a = a := Int32.toBitVec_inj.1 (BitVec.one_mul _)
@[simp] theorem Int64.one_mul (a : Int64) : 1 * a = a := Int64.toBitVec_inj.1 (BitVec.one_mul _)
@[simp] theorem ISize.one_mul (a : ISize) : 1 * a = a := ISize.toBitVec_inj.1 (BitVec.one_mul _)

instance : Std.LawfulCommIdentity (α := Int8) (· * ·) 1 where
  right_id := Int8.mul_one
instance : Std.LawfulCommIdentity (α := Int16) (· * ·) 1 where
  right_id := Int16.mul_one
instance : Std.LawfulCommIdentity (α := Int32) (· * ·) 1 where
  right_id := Int32.mul_one
instance : Std.LawfulCommIdentity (α := Int64) (· * ·) 1 where
  right_id := Int64.mul_one
instance : Std.LawfulCommIdentity (α := ISize) (· * ·) 1 where
  right_id := ISize.mul_one

@[simp] theorem Int8.mul_zero {a : Int8} : a * 0 = 0 := Int8.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem Int16.mul_zero {a : Int16} : a * 0 = 0 := Int16.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem Int32.mul_zero {a : Int32} : a * 0 = 0 := Int32.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem Int64.mul_zero {a : Int64} : a * 0 = 0 := Int64.toBitVec_inj.1 BitVec.mul_zero
@[simp] theorem ISize.mul_zero {a : ISize} : a * 0 = 0 := ISize.toBitVec_inj.1 BitVec.mul_zero

@[simp] theorem Int8.zero_mul {a : Int8} : 0 * a = 0 := Int8.toBitVec_inj.1 BitVec.zero_mul
@[simp] theorem Int16.zero_mul {a : Int16} : 0 * a = 0 := Int16.toBitVec_inj.1 BitVec.zero_mul
@[simp] theorem Int32.zero_mul {a : Int32} : 0 * a = 0 := Int32.toBitVec_inj.1 BitVec.zero_mul
@[simp] theorem Int64.zero_mul {a : Int64} : 0 * a = 0 := Int64.toBitVec_inj.1 BitVec.zero_mul
@[simp] theorem ISize.zero_mul {a : ISize} : 0 * a = 0 := ISize.toBitVec_inj.1 BitVec.zero_mul

@[simp] protected theorem Int8.pow_zero (x : Int8) : x ^ 0 = 1 := (rfl)
protected theorem Int8.pow_succ (x : Int8) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)
@[simp] protected theorem Int16.pow_zero (x : Int16) : x ^ 0 = 1 := (rfl)
protected theorem Int16.pow_succ (x : Int16) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)
@[simp] protected theorem Int32.pow_zero (x : Int32) : x ^ 0 = 1 := (rfl)
protected theorem Int32.pow_succ (x : Int32) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)
@[simp] protected theorem Int64.pow_zero (x : Int64) : x ^ 0 = 1 := (rfl)
protected theorem Int64.pow_succ (x : Int64) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)
@[simp] protected theorem ISize.pow_zero (x : ISize) : x ^ 0 = 1 := (rfl)
protected theorem ISize.pow_succ (x : ISize) (n : Nat) : x ^ (n + 1) = x ^ n * x := (rfl)

protected theorem Int8.mul_add {a b c : Int8} : a * (b + c) = a * b + a * c :=
    Int8.toBitVec_inj.1 BitVec.mul_add
protected theorem Int16.mul_add {a b c : Int16} : a * (b + c) = a * b + a * c :=
    Int16.toBitVec_inj.1 BitVec.mul_add
protected theorem Int32.mul_add {a b c : Int32} : a * (b + c) = a * b + a * c :=
    Int32.toBitVec_inj.1 BitVec.mul_add
protected theorem Int64.mul_add {a b c : Int64} : a * (b + c) = a * b + a * c :=
    Int64.toBitVec_inj.1 BitVec.mul_add
protected theorem ISize.mul_add {a b c : ISize} : a * (b + c) = a * b + a * c :=
    ISize.toBitVec_inj.1 BitVec.mul_add

protected theorem Int8.add_mul {a b c : Int8} : (a + b) * c = a * c + b * c := by
  rw [Int8.mul_comm, Int8.mul_add, Int8.mul_comm a c, Int8.mul_comm c b]
protected theorem Int16.add_mul {a b c : Int16} : (a + b) * c = a * c + b * c := by
  rw [Int16.mul_comm, Int16.mul_add, Int16.mul_comm a c, Int16.mul_comm c b]
protected theorem Int32.add_mul {a b c : Int32} : (a + b) * c = a * c + b * c := by
  rw [Int32.mul_comm, Int32.mul_add, Int32.mul_comm a c, Int32.mul_comm c b]
protected theorem Int64.add_mul {a b c : Int64} : (a + b) * c = a * c + b * c := by
  rw [Int64.mul_comm, Int64.mul_add, Int64.mul_comm a c, Int64.mul_comm c b]
protected theorem ISize.add_mul {a b c : ISize} : (a + b) * c = a * c + b * c := by
  rw [ISize.mul_comm, ISize.mul_add, ISize.mul_comm a c, ISize.mul_comm c b]

protected theorem Int8.mul_succ {a b : Int8} : a * (b + 1) = a * b + a := by simp [Int8.mul_add]
protected theorem Int16.mul_succ {a b : Int16} : a * (b + 1) = a * b + a := by simp [Int16.mul_add]
protected theorem Int32.mul_succ {a b : Int32} : a * (b + 1) = a * b + a := by simp [Int32.mul_add]
protected theorem Int64.mul_succ {a b : Int64} : a * (b + 1) = a * b + a := by simp [Int64.mul_add]
protected theorem ISize.mul_succ {a b : ISize} : a * (b + 1) = a * b + a := by simp [ISize.mul_add]

protected theorem Int8.succ_mul {a b : Int8} : (a + 1) * b = a * b + b := by simp [Int8.add_mul]
protected theorem Int16.succ_mul {a b : Int16} : (a + 1) * b = a * b + b := by simp [Int16.add_mul]
protected theorem Int32.succ_mul {a b : Int32} : (a + 1) * b = a * b + b := by simp [Int32.add_mul]
protected theorem Int64.succ_mul {a b : Int64} : (a + 1) * b = a * b + b := by simp [Int64.add_mul]
protected theorem ISize.succ_mul {a b : ISize} : (a + 1) * b = a * b + b := by simp [ISize.add_mul]

protected theorem Int8.two_mul {a : Int8} : 2 * a = a + a := Int8.toBitVec_inj.1 BitVec.two_mul
protected theorem Int16.two_mul {a : Int16} : 2 * a = a + a := Int16.toBitVec_inj.1 BitVec.two_mul
protected theorem Int32.two_mul {a : Int32} : 2 * a = a + a := Int32.toBitVec_inj.1 BitVec.two_mul
protected theorem Int64.two_mul {a : Int64} : 2 * a = a + a := Int64.toBitVec_inj.1 BitVec.two_mul
protected theorem ISize.two_mul {a : ISize} : 2 * a = a + a := ISize.toBitVec_inj.1 BitVec.two_mul

protected theorem Int8.mul_two {a : Int8} : a * 2 = a + a := Int8.toBitVec_inj.1 BitVec.mul_two
protected theorem Int16.mul_two {a : Int16} : a * 2 = a + a := Int16.toBitVec_inj.1 BitVec.mul_two
protected theorem Int32.mul_two {a : Int32} : a * 2 = a + a := Int32.toBitVec_inj.1 BitVec.mul_two
protected theorem Int64.mul_two {a : Int64} : a * 2 = a + a := Int64.toBitVec_inj.1 BitVec.mul_two
protected theorem ISize.mul_two {a : ISize} : a * 2 = a + a := ISize.toBitVec_inj.1 BitVec.mul_two

protected theorem Int8.neg_mul (a b : Int8) : -a * b = -(a * b) := Int8.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem Int16.neg_mul (a b : Int16) : -a * b = -(a * b) := Int16.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem Int32.neg_mul (a b : Int32) : -a * b = -(a * b) := Int32.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem Int64.neg_mul (a b : Int64) : -a * b = -(a * b) := Int64.toBitVec_inj.1 (BitVec.neg_mul _ _)
protected theorem ISize.neg_mul (a b : ISize) : -a * b = -(a * b) := ISize.toBitVec_inj.1 (BitVec.neg_mul _ _)

protected theorem Int8.mul_neg (a b : Int8) : a * -b = -(a * b) := Int8.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem Int16.mul_neg (a b : Int16) : a * -b = -(a * b) := Int16.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem Int32.mul_neg (a b : Int32) : a * -b = -(a * b) := Int32.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem Int64.mul_neg (a b : Int64) : a * -b = -(a * b) := Int64.toBitVec_inj.1 (BitVec.mul_neg _ _)
protected theorem ISize.mul_neg (a b : ISize) : a * -b = -(a * b) := ISize.toBitVec_inj.1 (BitVec.mul_neg _ _)

protected theorem Int8.neg_mul_neg (a b : Int8) : -a * -b = a * b := Int8.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem Int16.neg_mul_neg (a b : Int16) : -a * -b = a * b := Int16.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem Int32.neg_mul_neg (a b : Int32) : -a * -b = a * b := Int32.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem Int64.neg_mul_neg (a b : Int64) : -a * -b = a * b := Int64.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)
protected theorem ISize.neg_mul_neg (a b : ISize) : -a * -b = a * b := ISize.toBitVec_inj.1 (BitVec.neg_mul_neg _ _)

protected theorem Int8.neg_mul_comm (a b : Int8) : -a * b = a * -b := Int8.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)
protected theorem Int16.neg_mul_comm (a b : Int16) : -a * b = a * -b := Int16.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)
protected theorem Int32.neg_mul_comm (a b : Int32) : -a * b = a * -b := Int32.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)
protected theorem Int64.neg_mul_comm (a b : Int64) : -a * b = a * -b := Int64.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)
protected theorem ISize.neg_mul_comm (a b : ISize) : -a * b = a * -b := ISize.toBitVec_inj.1 (BitVec.neg_mul_comm _ _)

protected theorem Int8.mul_sub {a b c : Int8} : a * (b - c) = a * b - a * c := Int8.toBitVec_inj.1 BitVec.mul_sub
protected theorem Int16.mul_sub {a b c : Int16} : a * (b - c) = a * b - a * c := Int16.toBitVec_inj.1 BitVec.mul_sub
protected theorem Int32.mul_sub {a b c : Int32} : a * (b - c) = a * b - a * c := Int32.toBitVec_inj.1 BitVec.mul_sub
protected theorem Int64.mul_sub {a b c : Int64} : a * (b - c) = a * b - a * c := Int64.toBitVec_inj.1 BitVec.mul_sub
protected theorem ISize.mul_sub {a b c : ISize} : a * (b - c) = a * b - a * c := ISize.toBitVec_inj.1 BitVec.mul_sub

protected theorem Int8.sub_mul {a b c : Int8} : (a - b) * c = a * c - b * c := by
  rw [Int8.mul_comm, Int8.mul_sub, Int8.mul_comm, Int8.mul_comm c]
protected theorem Int16.sub_mul {a b c : Int16} : (a - b) * c = a * c - b * c := by
  rw [Int16.mul_comm, Int16.mul_sub, Int16.mul_comm, Int16.mul_comm c]
protected theorem Int32.sub_mul {a b c : Int32} : (a - b) * c = a * c - b * c := by
  rw [Int32.mul_comm, Int32.mul_sub, Int32.mul_comm, Int32.mul_comm c]
protected theorem Int64.sub_mul {a b c : Int64} : (a - b) * c = a * c - b * c := by
  rw [Int64.mul_comm, Int64.mul_sub, Int64.mul_comm, Int64.mul_comm c]
protected theorem ISize.sub_mul {a b c : ISize} : (a - b) * c = a * c - b * c := by
  rw [ISize.mul_comm, ISize.mul_sub, ISize.mul_comm, ISize.mul_comm c]

theorem Int8.neg_add_mul_eq_mul_not {a b : Int8} : -(a + a * b) = a * ~~~b :=
  Int8.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not
theorem Int16.neg_add_mul_eq_mul_not {a b : Int16} : -(a + a * b) = a * ~~~b :=
  Int16.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not
theorem Int32.neg_add_mul_eq_mul_not {a b : Int32} : -(a + a * b) = a * ~~~b :=
  Int32.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not
theorem Int64.neg_add_mul_eq_mul_not {a b : Int64} : -(a + a * b) = a * ~~~b :=
  Int64.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not
theorem ISize.neg_add_mul_eq_mul_not {a b : ISize} : -(a + a * b) = a * ~~~b :=
  ISize.toBitVec_inj.1 BitVec.neg_add_mul_eq_mul_not

theorem Int8.neg_mul_not_eq_add_mul {a b : Int8} : -(a * ~~~b) = a + a * b :=
  Int8.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul
theorem Int16.neg_mul_not_eq_add_mul {a b : Int16} : -(a * ~~~b) = a + a * b :=
  Int16.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul
theorem Int32.neg_mul_not_eq_add_mul {a b : Int32} : -(a * ~~~b) = a + a * b :=
  Int32.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul
theorem Int64.neg_mul_not_eq_add_mul {a b : Int64} : -(a * ~~~b) = a + a * b :=
  Int64.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul
theorem ISize.neg_mul_not_eq_add_mul {a b : ISize} : -(a * ~~~b) = a + a * b :=
  ISize.toBitVec_inj.1 BitVec.neg_mul_not_eq_add_mul

protected theorem Int8.le_of_lt {a b : Int8} : a < b → a ≤ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le] using Int.le_of_lt
protected theorem Int16.le_of_lt {a b : Int16} : a < b → a ≤ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le] using Int.le_of_lt
protected theorem Int32.le_of_lt {a b : Int32} : a < b → a ≤ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le] using Int.le_of_lt
protected theorem Int64.le_of_lt {a b : Int64} : a < b → a ≤ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le] using Int.le_of_lt
protected theorem ISize.le_of_lt {a b : ISize} : a < b → a ≤ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le] using Int.le_of_lt

protected theorem Int8.lt_of_le_of_ne {a b : Int8} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int8.toInt_inj] using (Int.lt_iff_le_and_ne.2 ⟨·, ·⟩)
protected theorem Int16.lt_of_le_of_ne {a b : Int16} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int16.toInt_inj] using (Int.lt_iff_le_and_ne.2 ⟨·, ·⟩)
protected theorem Int32.lt_of_le_of_ne {a b : Int32} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int32.toInt_inj] using (Int.lt_iff_le_and_ne.2 ⟨·, ·⟩)
protected theorem Int64.lt_of_le_of_ne {a b : Int64} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int64.toInt_inj] using (Int.lt_iff_le_and_ne.2 ⟨·, ·⟩)
protected theorem ISize.lt_of_le_of_ne {a b : ISize} : a ≤ b → a ≠ b → a < b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← ISize.toInt_inj] using (Int.lt_iff_le_and_ne.2 ⟨·, ·⟩)

protected theorem Int8.lt_iff_le_and_ne {a b : Int8} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int8.toInt_inj] using Int.lt_iff_le_and_ne
protected theorem Int16.lt_iff_le_and_ne {a b : Int16} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int16.toInt_inj] using Int.lt_iff_le_and_ne
protected theorem Int32.lt_iff_le_and_ne {a b : Int32} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int32.toInt_inj] using Int.lt_iff_le_and_ne
protected theorem Int64.lt_iff_le_and_ne {a b : Int64} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← Int64.toInt_inj] using Int.lt_iff_le_and_ne
protected theorem ISize.lt_iff_le_and_ne {a b : ISize} : a < b ↔ a ≤ b ∧ a ≠ b := by
  simpa [lt_iff_toInt_lt, le_iff_toInt_le, ← ISize.toInt_inj] using Int.lt_iff_le_and_ne

@[simp] protected theorem Int8.lt_irrefl {a : Int8} : ¬a < a := by simp [lt_iff_toInt_lt]
@[simp] protected theorem Int16.lt_irrefl {a : Int16} : ¬a < a := by simp [lt_iff_toInt_lt]
@[simp] protected theorem Int32.lt_irrefl {a : Int32} : ¬a < a := by simp [lt_iff_toInt_lt]
@[simp] protected theorem Int64.lt_irrefl {a : Int64} : ¬a < a := by simp [lt_iff_toInt_lt]
@[simp] protected theorem ISize.lt_irrefl {a : ISize} : ¬a < a := by simp [lt_iff_toInt_lt]

protected theorem Int8.lt_of_le_of_lt {a b c : Int8} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_le_of_lt
protected theorem Int16.lt_of_le_of_lt {a b c : Int16} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_le_of_lt
protected theorem Int32.lt_of_le_of_lt {a b c : Int32} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_le_of_lt
protected theorem Int64.lt_of_le_of_lt {a b c : Int64} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_le_of_lt
protected theorem ISize.lt_of_le_of_lt {a b c : ISize} : a ≤ b → b < c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_le_of_lt

protected theorem Int8.lt_of_lt_of_le {a b c : Int8} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_lt_of_le
protected theorem Int16.lt_of_lt_of_le {a b c : Int16} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_lt_of_le
protected theorem Int32.lt_of_lt_of_le {a b c : Int32} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_lt_of_le
protected theorem Int64.lt_of_lt_of_le {a b c : Int64} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_lt_of_le
protected theorem ISize.lt_of_lt_of_le {a b c : ISize} : a < b → b ≤ c → a < c := by
  simpa [le_iff_toInt_le, lt_iff_toInt_lt] using Int.lt_of_lt_of_le

@[simp] theorem Int8.minValue_le (a : Int8) : minValue ≤ a := by simpa [le_iff_toInt_le] using a.minValue_le_toInt
@[simp] theorem Int16.minValue_le (a : Int16) : minValue ≤ a := by simpa [le_iff_toInt_le] using a.minValue_le_toInt
@[simp] theorem Int32.minValue_le (a : Int32) : minValue ≤ a := by simpa [le_iff_toInt_le] using a.minValue_le_toInt
@[simp] theorem Int64.minValue_le (a : Int64) : minValue ≤ a := by simpa [le_iff_toInt_le] using a.minValue_le_toInt
@[simp] theorem ISize.minValue_le (a : ISize) : minValue ≤ a := by simpa [le_iff_toInt_le] using a.minValue_le_toInt

@[simp] theorem Int8.le_maxValue (a : Int8) : a ≤ maxValue := by simpa [le_iff_toInt_le] using a.toInt_le
@[simp] theorem Int16.le_maxValue (a : Int16) : a ≤ maxValue := by simpa [le_iff_toInt_le] using a.toInt_le
@[simp] theorem Int32.le_maxValue (a : Int32) : a ≤ maxValue := by simpa [le_iff_toInt_le] using a.toInt_le
@[simp] theorem Int64.le_maxValue (a : Int64) : a ≤ maxValue := by simpa [le_iff_toInt_le] using a.toInt_le
@[simp] theorem ISize.le_maxValue (a : ISize) : a ≤ maxValue := by simpa [le_iff_toInt_le] using a.toInt_le

@[simp] theorem Int8.not_lt_minValue {a : Int8} : ¬a < minValue :=
  fun h => Int8.lt_irrefl (Int8.lt_of_le_of_lt a.minValue_le h)
@[simp] theorem Int16.not_lt_minValue {a : Int16} : ¬a < minValue :=
  fun h => Int16.lt_irrefl (Int16.lt_of_le_of_lt a.minValue_le h)
@[simp] theorem Int32.not_lt_minValue {a : Int32} : ¬a < minValue :=
  fun h => Int32.lt_irrefl (Int32.lt_of_le_of_lt a.minValue_le h)
@[simp] theorem Int64.not_lt_minValue {a : Int64} : ¬a < minValue :=
  fun h => Int64.lt_irrefl (Int64.lt_of_le_of_lt a.minValue_le h)
@[simp] theorem ISize.not_lt_minValue {a : ISize} : ¬a < minValue :=
  fun h => ISize.lt_irrefl (ISize.lt_of_le_of_lt a.minValue_le h)

@[simp] theorem Int8.not_maxValue_lt {a : Int8} : ¬maxValue < a :=
  fun h => Int8.lt_irrefl (Int8.lt_of_lt_of_le h a.le_maxValue)
@[simp] theorem Int16.not_maxValue_lt {a : Int16} : ¬maxValue < a :=
  fun h => Int16.lt_irrefl (Int16.lt_of_lt_of_le h a.le_maxValue)
@[simp] theorem Int32.not_maxValue_lt {a : Int32} : ¬maxValue < a :=
  fun h => Int32.lt_irrefl (Int32.lt_of_lt_of_le h a.le_maxValue)
@[simp] theorem Int64.not_maxValue_lt {a : Int64} : ¬maxValue < a :=
  fun h => Int64.lt_irrefl (Int64.lt_of_lt_of_le h a.le_maxValue)
@[simp] theorem ISize.not_maxValue_lt {a : ISize} : ¬maxValue < a :=
  fun h => ISize.lt_irrefl (ISize.lt_of_lt_of_le h a.le_maxValue)

@[simp] protected theorem Int8.le_refl (a : Int8) : a ≤ a := by simp [Int8.le_iff_toInt_le]
@[simp] protected theorem Int16.le_refl (a : Int16) : a ≤ a := by simp [Int16.le_iff_toInt_le]
@[simp] protected theorem Int32.le_refl (a : Int32) : a ≤ a := by simp [Int32.le_iff_toInt_le]
@[simp] protected theorem Int64.le_refl (a : Int64) : a ≤ a := by simp [Int64.le_iff_toInt_le]
@[simp] protected theorem ISize.le_refl (a : ISize) : a ≤ a := by simp [ISize.le_iff_toInt_le]

protected theorem Int8.le_rfl {a : Int8} : a ≤ a := Int8.le_refl _
protected theorem Int16.le_rfl {a : Int16} : a ≤ a := Int16.le_refl _
protected theorem Int32.le_rfl {a : Int32} : a ≤ a := Int32.le_refl _
protected theorem Int64.le_rfl {a : Int64} : a ≤ a := Int64.le_refl _
protected theorem ISize.le_rfl {a : ISize} : a ≤ a := ISize.le_refl _

protected theorem Int8.le_antisymm_iff {a b : Int8} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨by rintro rfl; simp, by simpa [← Int8.toInt_inj, le_iff_toInt_le] using Int.le_antisymm⟩
protected theorem Int16.le_antisymm_iff {a b : Int16} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨by rintro rfl; simp, by simpa [← Int16.toInt_inj, le_iff_toInt_le] using Int.le_antisymm⟩
protected theorem Int32.le_antisymm_iff {a b : Int32} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨by rintro rfl; simp, by simpa [← Int32.toInt_inj, le_iff_toInt_le] using Int.le_antisymm⟩
protected theorem Int64.le_antisymm_iff {a b : Int64} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨by rintro rfl; simp, by simpa [← Int64.toInt_inj, le_iff_toInt_le] using Int.le_antisymm⟩
protected theorem ISize.le_antisymm_iff {a b : ISize} : a = b ↔ a ≤ b ∧ b ≤ a :=
  ⟨by rintro rfl; simp, by simpa [← ISize.toInt_inj, le_iff_toInt_le] using Int.le_antisymm⟩

protected theorem Int8.le_antisymm {a b : Int8} : a ≤ b → b ≤ a → a = b := by simpa using Int8.le_antisymm_iff.2
protected theorem Int16.le_antisymm {a b : Int16} : a ≤ b → b ≤ a → a = b := by simpa using Int16.le_antisymm_iff.2
protected theorem Int32.le_antisymm {a b : Int32} : a ≤ b → b ≤ a → a = b := by simpa using Int32.le_antisymm_iff.2
protected theorem Int64.le_antisymm {a b : Int64} : a ≤ b → b ≤ a → a = b := by simpa using Int64.le_antisymm_iff.2
protected theorem ISize.le_antisymm {a b : ISize} : a ≤ b → b ≤ a → a = b := by simpa using ISize.le_antisymm_iff.2

@[simp] theorem Int8.le_minValue_iff {a : Int8} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => Int8.le_antisymm h a.minValue_le, by rintro rfl; simp⟩
@[simp] theorem Int16.le_minValue_iff {a : Int16} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => Int16.le_antisymm h a.minValue_le, by rintro rfl; simp⟩
@[simp] theorem Int32.le_minValue_iff {a : Int32} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => Int32.le_antisymm h a.minValue_le, by rintro rfl; simp⟩
@[simp] theorem Int64.le_minValue_iff {a : Int64} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => Int64.le_antisymm h a.minValue_le, by rintro rfl; simp⟩
@[simp] theorem ISize.le_minValue_iff {a : ISize} : a ≤ minValue ↔ a = minValue :=
  ⟨fun h => ISize.le_antisymm h a.minValue_le, by rintro rfl; simp⟩

@[simp] theorem Int8.maxValue_le_iff {a : Int8} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => Int8.le_antisymm a.le_maxValue h, by rintro rfl; simp⟩
@[simp] theorem Int16.maxValue_le_iff {a : Int16} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => Int16.le_antisymm a.le_maxValue h, by rintro rfl; simp⟩
@[simp] theorem Int32.maxValue_le_iff {a : Int32} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => Int32.le_antisymm a.le_maxValue h, by rintro rfl; simp⟩
@[simp] theorem Int64.maxValue_le_iff {a : Int64} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => Int64.le_antisymm a.le_maxValue h, by rintro rfl; simp⟩
@[simp] theorem ISize.maxValue_le_iff {a : ISize} : maxValue ≤ a ↔ a = maxValue :=
  ⟨fun h => ISize.le_antisymm a.le_maxValue h, by rintro rfl; simp⟩

@[simp] protected theorem Int8.zero_div {a : Int8} : 0 / a = 0 := Int8.toBitVec_inj.1 BitVec.zero_sdiv
@[simp] protected theorem Int16.zero_div {a : Int16} : 0 / a = 0 := Int16.toBitVec_inj.1 BitVec.zero_sdiv
@[simp] protected theorem Int32.zero_div {a : Int32} : 0 / a = 0 := Int32.toBitVec_inj.1 BitVec.zero_sdiv
@[simp] protected theorem Int64.zero_div {a : Int64} : 0 / a = 0 := Int64.toBitVec_inj.1 BitVec.zero_sdiv
@[simp] protected theorem ISize.zero_div {a : ISize} : 0 / a = 0 := ISize.toBitVec_inj.1 BitVec.zero_sdiv

@[simp] protected theorem Int8.div_zero {a : Int8} : a / 0 = 0 := Int8.toBitVec_inj.1 BitVec.sdiv_zero
@[simp] protected theorem Int16.div_zero {a : Int16} : a / 0 = 0 := Int16.toBitVec_inj.1 BitVec.sdiv_zero
@[simp] protected theorem Int32.div_zero {a : Int32} : a / 0 = 0 := Int32.toBitVec_inj.1 BitVec.sdiv_zero
@[simp] protected theorem Int64.div_zero {a : Int64} : a / 0 = 0 := Int64.toBitVec_inj.1 BitVec.sdiv_zero
@[simp] protected theorem ISize.div_zero {a : ISize} : a / 0 = 0 := ISize.toBitVec_inj.1 BitVec.sdiv_zero

@[simp] protected theorem Int8.div_one {a : Int8} : a / 1 = a := Int8.toBitVec_inj.1 BitVec.sdiv_one
@[simp] protected theorem Int16.div_one {a : Int16} : a / 1 = a := Int16.toBitVec_inj.1 BitVec.sdiv_one
@[simp] protected theorem Int32.div_one {a : Int32} : a / 1 = a := Int32.toBitVec_inj.1 BitVec.sdiv_one
@[simp] protected theorem Int64.div_one {a : Int64} : a / 1 = a := Int64.toBitVec_inj.1 BitVec.sdiv_one
@[simp] protected theorem ISize.div_one {a : ISize} : a / 1 = a := ISize.toBitVec_inj.1 BitVec.sdiv_one

protected theorem Int8.div_self {a : Int8} : a / a = if a = 0 then 0 else 1 := by
  simp [← Int8.toBitVec_inj, apply_ite]
protected theorem Int16.div_self {a : Int16} : a / a = if a = 0 then 0 else 1 := by
  simp [← Int16.toBitVec_inj, apply_ite]
protected theorem Int32.div_self {a : Int32} : a / a = if a = 0 then 0 else 1 := by
  simp [← Int32.toBitVec_inj, apply_ite]
protected theorem Int64.div_self {a : Int64} : a / a = if a = 0 then 0 else 1 := by
  simp [← Int64.toBitVec_inj, apply_ite]
protected theorem ISize.div_self {a : ISize} : a / a = if a = 0 then 0 else 1 := by
  simp [← ISize.toInt_inj]
  split
  · simp_all
  · rw [Int.tdiv_self, Int.bmod_eq_of_le]
    · simp
    · cases System.Platform.numBits_eq <;> simp_all
    · cases System.Platform.numBits_eq <;> simp_all
    · cases System.Platform.numBits_eq <;> simp_all

@[simp] protected theorem Int8.mod_zero {a : Int8} : a % 0 = a := Int8.toBitVec_inj.1 BitVec.srem_zero
@[simp] protected theorem Int16.mod_zero {a : Int16} : a % 0 = a := Int16.toBitVec_inj.1 BitVec.srem_zero
@[simp] protected theorem Int32.mod_zero {a : Int32} : a % 0 = a := Int32.toBitVec_inj.1 BitVec.srem_zero
@[simp] protected theorem Int64.mod_zero {a : Int64} : a % 0 = a := Int64.toBitVec_inj.1 BitVec.srem_zero
@[simp] protected theorem ISize.mod_zero {a : ISize} : a % 0 = a := ISize.toBitVec_inj.1 BitVec.srem_zero

@[simp] protected theorem Int8.zero_mod {a : Int8} : 0 % a = 0 := Int8.toBitVec_inj.1 BitVec.zero_srem
@[simp] protected theorem Int16.zero_mod {a : Int16} : 0 % a = 0 := Int16.toBitVec_inj.1 BitVec.zero_srem
@[simp] protected theorem Int32.zero_mod {a : Int32} : 0 % a = 0 := Int32.toBitVec_inj.1 BitVec.zero_srem
@[simp] protected theorem Int64.zero_mod {a : Int64} : 0 % a = 0 := Int64.toBitVec_inj.1 BitVec.zero_srem
@[simp] protected theorem ISize.zero_mod {a : ISize} : 0 % a = 0 := ISize.toBitVec_inj.1 BitVec.zero_srem

@[simp] protected theorem Int8.mod_one {a : Int8} : a % 1 = 0 := Int8.toBitVec_inj.1 BitVec.srem_one
@[simp] protected theorem Int16.mod_one {a : Int16} : a % 1 = 0 := Int16.toBitVec_inj.1 BitVec.srem_one
@[simp] protected theorem Int32.mod_one {a : Int32} : a % 1 = 0 := Int32.toBitVec_inj.1 BitVec.srem_one
@[simp] protected theorem Int64.mod_one {a : Int64} : a % 1 = 0 := Int64.toBitVec_inj.1 BitVec.srem_one
@[simp] protected theorem ISize.mod_one {a : ISize} : a % 1 = 0 := ISize.toBitVec_inj.1 BitVec.srem_one

@[simp] protected theorem Int8.mod_self {a : Int8} : a % a = 0 := Int8.toBitVec_inj.1 BitVec.srem_self
@[simp] protected theorem Int16.mod_self {a : Int16} : a % a = 0 := Int16.toBitVec_inj.1 BitVec.srem_self
@[simp] protected theorem Int32.mod_self {a : Int32} : a % a = 0 := Int32.toBitVec_inj.1 BitVec.srem_self
@[simp] protected theorem Int64.mod_self {a : Int64} : a % a = 0 := Int64.toBitVec_inj.1 BitVec.srem_self
@[simp] protected theorem ISize.mod_self {a : ISize} : a % a = 0 := ISize.toBitVec_inj.1 BitVec.srem_self

@[simp] protected theorem Int8.not_lt {a b : Int8} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]
@[simp] protected theorem Int16.not_lt {a b : Int16} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]
@[simp] protected theorem Int32.not_lt {a b : Int32} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]
@[simp] protected theorem Int64.not_lt {a b : Int64} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]
@[simp] protected theorem ISize.not_lt {a b : ISize} : ¬ a < b ↔ b ≤ a := by
  simp [lt_iff_toBitVec_slt, le_iff_toBitVec_sle, BitVec.sle_eq_not_slt]

protected theorem Int8.le_trans {a b c : Int8} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff_toInt_le] using Int.le_trans
protected theorem Int16.le_trans {a b c : Int16} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff_toInt_le] using Int.le_trans
protected theorem Int32.le_trans {a b c : Int32} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff_toInt_le] using Int.le_trans
protected theorem Int64.le_trans {a b c : Int64} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff_toInt_le] using Int.le_trans
protected theorem ISize.le_trans {a b c : ISize} : a ≤ b → b ≤ c → a ≤ c := by
  simpa [le_iff_toInt_le] using Int.le_trans

protected theorem Int8.lt_trans {a b c : Int8} : a < b → b < c → a < c := by
  simpa [lt_iff_toInt_lt] using Int.lt_trans
protected theorem Int16.lt_trans {a b c : Int16} : a < b → b < c → a < c := by
  simpa [lt_iff_toInt_lt] using Int.lt_trans
protected theorem Int32.lt_trans {a b c : Int32} : a < b → b < c → a < c := by
  simpa [lt_iff_toInt_lt] using Int.lt_trans
protected theorem Int64.lt_trans {a b c : Int64} : a < b → b < c → a < c := by
  simpa [lt_iff_toInt_lt] using Int.lt_trans
protected theorem ISize.lt_trans {a b c : ISize} : a < b → b < c → a < c := by
  simpa [lt_iff_toInt_lt] using Int.lt_trans

protected theorem Int8.le_total (a b : Int8) : a ≤ b ∨ b ≤ a := by
  simpa [le_iff_toInt_le] using Int.le_total _ _
protected theorem Int16.le_total (a b : Int16) : a ≤ b ∨ b ≤ a := by
  simpa [le_iff_toInt_le] using Int.le_total _ _
protected theorem Int32.le_total (a b : Int32) : a ≤ b ∨ b ≤ a := by
  simpa [le_iff_toInt_le] using Int.le_total _ _
protected theorem Int64.le_total (a b : Int64) : a ≤ b ∨ b ≤ a := by
  simpa [le_iff_toInt_le] using Int.le_total _ _
protected theorem ISize.le_total (a b : ISize) : a ≤ b ∨ b ≤ a := by
  simpa [le_iff_toInt_le] using Int.le_total _ _

protected theorem Int8.lt_asymm {a b : Int8} : a < b → ¬b < a :=
  fun hab hba => Int8.lt_irrefl (Int8.lt_trans hab hba)
protected theorem Int16.lt_asymm {a b : Int16} : a < b → ¬b < a :=
  fun hab hba => Int16.lt_irrefl (Int16.lt_trans hab hba)
protected theorem Int32.lt_asymm {a b : Int32} : a < b → ¬b < a :=
  fun hab hba => Int32.lt_irrefl (Int32.lt_trans hab hba)
protected theorem Int64.lt_asymm {a b : Int64} : a < b → ¬b < a :=
  fun hab hba => Int64.lt_irrefl (Int64.lt_trans hab hba)
protected theorem ISize.lt_asymm {a b : ISize} : a < b → ¬b < a :=
  fun hab hba => ISize.lt_irrefl (ISize.lt_trans hab hba)

protected theorem Int8.add_neg_eq_sub {a b : Int8} : a + -b = a - b := Int8.toBitVec_inj.1 BitVec.add_neg_eq_sub
protected theorem Int16.add_neg_eq_sub {a b : Int16} : a + -b = a - b := Int16.toBitVec_inj.1 BitVec.add_neg_eq_sub
protected theorem Int32.add_neg_eq_sub {a b : Int32} : a + -b = a - b := Int32.toBitVec_inj.1 BitVec.add_neg_eq_sub
protected theorem Int64.add_neg_eq_sub {a b : Int64} : a + -b = a - b := Int64.toBitVec_inj.1 BitVec.add_neg_eq_sub
protected theorem ISize.add_neg_eq_sub {a b : ISize} : a + -b = a - b := ISize.toBitVec_inj.1 BitVec.add_neg_eq_sub

theorem Int8.neg_eq_neg_one_mul (a : Int8) : -a = -1 * a := Int8.toInt_inj.1 (by simp)
theorem Int16.neg_eq_neg_one_mul (a : Int16) : -a = -1 * a := Int16.toInt_inj.1 (by simp)
theorem Int32.neg_eq_neg_one_mul (a : Int32) : -a = -1 * a := Int32.toInt_inj.1 (by simp)
theorem Int64.neg_eq_neg_one_mul (a : Int64) : -a = -1 * a := Int64.toInt_inj.1 (by simp)
theorem ISize.neg_eq_neg_one_mul (a : ISize) : -a = -1 * a := ISize.toInt_inj.1 (by simp [toInt_neg])

@[simp] protected theorem Int8.add_sub_cancel (a b : Int8) : a + b - b = a := Int8.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)
@[simp] protected theorem Int16.add_sub_cancel (a b : Int16) : a + b - b = a := Int16.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)
@[simp] protected theorem Int32.add_sub_cancel (a b : Int32) : a + b - b = a := Int32.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)
@[simp] protected theorem Int64.add_sub_cancel (a b : Int64) : a + b - b = a := Int64.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)
@[simp] protected theorem ISize.add_sub_cancel (a b : ISize) : a + b - b = a := ISize.toBitVec_inj.1 (BitVec.add_sub_cancel _ _)

protected theorem Int8.lt_or_lt_of_ne {a b : Int8} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← Int8.toInt_inj]; omega
protected theorem Int16.lt_or_lt_of_ne {a b : Int16} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← Int16.toInt_inj]; omega
protected theorem Int32.lt_or_lt_of_ne {a b : Int32} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← Int32.toInt_inj]; omega
protected theorem Int64.lt_or_lt_of_ne {a b : Int64} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← Int64.toInt_inj]; omega
protected theorem ISize.lt_or_lt_of_ne {a b : ISize} : a ≠ b → a < b ∨ b < a := by
  simp [lt_iff_toInt_lt, ← ISize.toInt_inj]; omega

protected theorem Int8.lt_or_le (a b : Int8) : a < b ∨ b ≤ a := by
  simp [lt_iff_toInt_lt, le_iff_toInt_le]; omega
protected theorem Int16.lt_or_le (a b : Int16) : a < b ∨ b ≤ a := by
  simp [lt_iff_toInt_lt, le_iff_toInt_le]; omega
protected theorem Int32.lt_or_le (a b : Int32) : a < b ∨ b ≤ a := by
  simp [lt_iff_toInt_lt, le_iff_toInt_le]; omega
protected theorem Int64.lt_or_le (a b : Int64) : a < b ∨ b ≤ a := by
  simp [lt_iff_toInt_lt, le_iff_toInt_le]; omega
protected theorem ISize.lt_or_le (a b : ISize) : a < b ∨ b ≤ a := by
  simp [lt_iff_toInt_lt, le_iff_toInt_le]; omega

protected theorem Int8.le_or_lt (a b : Int8) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem Int16.le_or_lt (a b : Int16) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem Int32.le_or_lt (a b : Int32) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem Int64.le_or_lt (a b : Int64) : a ≤ b ∨ b < a := (b.lt_or_le a).symm
protected theorem ISize.le_or_lt (a b : ISize) : a ≤ b ∨ b < a := (b.lt_or_le a).symm

protected theorem Int8.le_of_eq {a b : Int8} : a = b → a ≤ b := (· ▸ Int8.le_rfl)
protected theorem Int16.le_of_eq {a b : Int16} : a = b → a ≤ b := (· ▸ Int16.le_rfl)
protected theorem Int32.le_of_eq {a b : Int32} : a = b → a ≤ b := (· ▸ Int32.le_rfl)
protected theorem Int64.le_of_eq {a b : Int64} : a = b → a ≤ b := (· ▸ Int64.le_rfl)
protected theorem ISize.le_of_eq {a b : ISize} : a = b → a ≤ b := (· ▸ ISize.le_rfl)

protected theorem Int8.le_iff_lt_or_eq {a b : Int8} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← Int8.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega
protected theorem Int16.le_iff_lt_or_eq {a b : Int16} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← Int16.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega
protected theorem Int32.le_iff_lt_or_eq {a b : Int32} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← Int32.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega
protected theorem Int64.le_iff_lt_or_eq {a b : Int64} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← Int64.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega
protected theorem ISize.le_iff_lt_or_eq {a b : ISize} : a ≤ b ↔ a < b ∨ a = b := by
  simp [← ISize.toInt_inj, le_iff_toInt_le, lt_iff_toInt_lt]; omega

protected theorem Int8.lt_or_eq_of_le {a b : Int8} : a ≤ b → a < b ∨ a = b := Int8.le_iff_lt_or_eq.mp
protected theorem Int16.lt_or_eq_of_le {a b : Int16} : a ≤ b → a < b ∨ a = b := Int16.le_iff_lt_or_eq.mp
protected theorem Int32.lt_or_eq_of_le {a b : Int32} : a ≤ b → a < b ∨ a = b := Int32.le_iff_lt_or_eq.mp
protected theorem Int64.lt_or_eq_of_le {a b : Int64} : a ≤ b → a < b ∨ a = b := Int64.le_iff_lt_or_eq.mp
protected theorem ISize.lt_or_eq_of_le {a b : ISize} : a ≤ b → a < b ∨ a = b := ISize.le_iff_lt_or_eq.mp

theorem Int8.toInt_eq_toNatClampNeg {a : Int8} (ha : 0 ≤ a) : a.toInt = a.toNatClampNeg := by
  simpa only [← toNat_toInt, Int.eq_natCast_toNat, le_iff_toInt_le] using ha
theorem Int16.toInt_eq_toNatClampNeg {a : Int16} (ha : 0 ≤ a) : a.toInt = a.toNatClampNeg := by
  simpa only [← toNat_toInt, Int.eq_natCast_toNat, le_iff_toInt_le] using ha
theorem Int32.toInt_eq_toNatClampNeg {a : Int32} (ha : 0 ≤ a) : a.toInt = a.toNatClampNeg := by
  simpa only [← toNat_toInt, Int.eq_natCast_toNat, le_iff_toInt_le] using ha
theorem Int64.toInt_eq_toNatClampNeg {a : Int64} (ha : 0 ≤ a) : a.toInt = a.toNatClampNeg := by
  simpa only [← toNat_toInt, Int.eq_natCast_toNat, le_iff_toInt_le] using ha
theorem ISize.toInt_eq_toNatClampNeg {a : ISize} (ha : 0 ≤ a) : a.toInt = a.toNatClampNeg := by
  simpa only [← toNat_toInt, Int.eq_natCast_toNat, le_iff_toInt_le, toInt_zero] using ha

@[simp] theorem UInt8.toInt8_add (a b : UInt8) : (a + b).toInt8 = a.toInt8 + b.toInt8 := (rfl)
@[simp] theorem UInt16.toInt16_add (a b : UInt16) : (a + b).toInt16 = a.toInt16 + b.toInt16 := (rfl)
@[simp] theorem UInt32.toInt32_add (a b : UInt32) : (a + b).toInt32 = a.toInt32 + b.toInt32 := (rfl)
@[simp] theorem UInt64.toInt64_add (a b : UInt64) : (a + b).toInt64 = a.toInt64 + b.toInt64 := (rfl)
@[simp] theorem USize.toISize_add (a b : USize) : (a + b).toISize = a.toISize + b.toISize := (rfl)

@[simp] theorem UInt8.toInt8_neg (a : UInt8) : (-a).toInt8 = -a.toInt8 := (rfl)
@[simp] theorem UInt16.toInt16_neg (a : UInt16) : (-a).toInt16 = -a.toInt16 := (rfl)
@[simp] theorem UInt32.toInt32_neg (a : UInt32) : (-a).toInt32 = -a.toInt32 := (rfl)
@[simp] theorem UInt64.toInt64_neg (a : UInt64) : (-a).toInt64 = -a.toInt64 := (rfl)
@[simp] theorem USize.toISize_neg (a : USize) : (-a).toISize = -a.toISize := (rfl)

@[simp] theorem UInt8.toInt8_sub (a b : UInt8) : (a - b).toInt8 = a.toInt8 - b.toInt8 := (rfl)
@[simp] theorem UInt16.toInt16_sub (a b : UInt16) : (a - b).toInt16 = a.toInt16 - b.toInt16 := (rfl)
@[simp] theorem UInt32.toInt32_sub (a b : UInt32) : (a - b).toInt32 = a.toInt32 - b.toInt32 := (rfl)
@[simp] theorem UInt64.toInt64_sub (a b : UInt64) : (a - b).toInt64 = a.toInt64 - b.toInt64 := (rfl)
@[simp] theorem USize.toISize_sub (a b : USize) : (a - b).toISize = a.toISize - b.toISize := (rfl)

@[simp] theorem UInt8.toInt8_mul (a b : UInt8) : (a * b).toInt8 = a.toInt8 * b.toInt8 := (rfl)
@[simp] theorem UInt16.toInt16_mul (a b : UInt16) : (a * b).toInt16 = a.toInt16 * b.toInt16 := (rfl)
@[simp] theorem UInt32.toInt32_mul (a b : UInt32) : (a * b).toInt32 = a.toInt32 * b.toInt32 := (rfl)
@[simp] theorem UInt64.toInt64_mul (a b : UInt64) : (a * b).toInt64 = a.toInt64 * b.toInt64 := (rfl)
@[simp] theorem USize.toISize_mul (a b : USize) : (a * b).toISize = a.toISize * b.toISize := (rfl)

@[simp] theorem Int8.toUInt8_add (a b : Int8) : (a + b).toUInt8 = a.toUInt8 + b.toUInt8 := (rfl)
@[simp] theorem Int16.toUInt16_add (a b : Int16) : (a + b).toUInt16 = a.toUInt16 + b.toUInt16 := (rfl)
@[simp] theorem Int32.toUInt32_add (a b : Int32) : (a + b).toUInt32 = a.toUInt32 + b.toUInt32 := (rfl)
@[simp] theorem Int64.toUInt64_add (a b : Int64) : (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := (rfl)
@[simp] theorem ISize.toUSize_add (a b : ISize) : (a + b).toUSize = a.toUSize + b.toUSize := (rfl)

@[simp] theorem Int8.toUInt8_neg (a : Int8) : (-a).toUInt8 = -a.toUInt8 := (rfl)
@[simp] theorem Int16.toUInt16_neg (a : Int16) : (-a).toUInt16 = -a.toUInt16 := (rfl)
@[simp] theorem Int32.toUInt32_neg (a : Int32) : (-a).toUInt32 = -a.toUInt32 := (rfl)
@[simp] theorem Int64.toUInt64_neg (a : Int64) : (-a).toUInt64 = -a.toUInt64 := (rfl)
@[simp] theorem ISize.toUSize_neg (a : ISize) : (-a).toUSize = -a.toUSize := (rfl)

@[simp] theorem Int8.toUInt8_sub (a b : Int8) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := (rfl)
@[simp] theorem Int16.toUInt16_sub (a b : Int16) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := (rfl)
@[simp] theorem Int32.toUInt32_sub (a b : Int32) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := (rfl)
@[simp] theorem Int64.toUInt64_sub (a b : Int64) : (a - b).toUInt64 = a.toUInt64 - b.toUInt64 := (rfl)
@[simp] theorem ISize.toUSize_sub (a b : ISize) : (a - b).toUSize = a.toUSize - b.toUSize := (rfl)

@[simp] theorem Int8.toUInt8_mul (a b : Int8) : (a * b).toUInt8 = a.toUInt8 * b.toUInt8 := (rfl)
@[simp] theorem Int16.toUInt16_mul (a b : Int16) : (a * b).toUInt16 = a.toUInt16 * b.toUInt16 := (rfl)
@[simp] theorem Int32.toUInt32_mul (a b : Int32) : (a * b).toUInt32 = a.toUInt32 * b.toUInt32 := (rfl)
@[simp] theorem Int64.toUInt64_mul (a b : Int64) : (a * b).toUInt64 = a.toUInt64 * b.toUInt64 := (rfl)
@[simp] theorem ISize.toUSize_mul (a b : ISize) : (a * b).toUSize = a.toUSize * b.toUSize := (rfl)

theorem Int8.toNatClampNeg_le {a b : Int8} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← Int8.toNat_toInt, ← Int8.toNat_toInt]
  exact Int.toNat_le_toNat (Int8.le_iff_toInt_le.1 hab)
theorem Int16.toNatClampNeg_le {a b : Int16} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← Int16.toNat_toInt, ← Int16.toNat_toInt]
  exact Int.toNat_le_toNat (Int16.le_iff_toInt_le.1 hab)
theorem Int32.toNatClampNeg_le {a b : Int32} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← Int32.toNat_toInt, ← Int32.toNat_toInt]
  exact Int.toNat_le_toNat (Int32.le_iff_toInt_le.1 hab)
theorem Int64.toNatClampNeg_le {a b : Int64} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← Int64.toNat_toInt, ← Int64.toNat_toInt]
  exact Int.toNat_le_toNat (Int64.le_iff_toInt_le.1 hab)
theorem ISize.toNatClampNeg_le {a b : ISize} (hab : a ≤ b) : a.toNatClampNeg ≤ b.toNatClampNeg := by
  rw [← ISize.toNat_toInt, ← ISize.toNat_toInt]
  exact Int.toNat_le_toNat (ISize.le_iff_toInt_le.1 hab)

theorem Int8.toUInt8_le {a b : Int8} (ha : 0 ≤ a) (hab : a ≤ b) : a.toUInt8 ≤ b.toUInt8 := by
  rw [UInt8.le_iff_toNat_le, toNat_toUInt8_of_le ha, toNat_toUInt8_of_le (Int8.le_trans ha hab)]
  exact Int8.toNatClampNeg_le hab
theorem Int16.toUInt16_le {a b : Int16} (ha : 0 ≤ a) (hab : a ≤ b) : a.toUInt16 ≤ b.toUInt16 := by
  rw [UInt16.le_iff_toNat_le, toNat_toUInt16_of_le ha, toNat_toUInt16_of_le (Int16.le_trans ha hab)]
  exact Int16.toNatClampNeg_le hab
theorem Int32.toUInt32_le {a b : Int32} (ha : 0 ≤ a) (hab : a ≤ b) : a.toUInt32 ≤ b.toUInt32 := by
  rw [UInt32.le_iff_toNat_le, toNat_toUInt32_of_le ha, toNat_toUInt32_of_le (Int32.le_trans ha hab)]
  exact Int32.toNatClampNeg_le hab
theorem Int64.toUInt64_le {a b : Int64} (ha : 0 ≤ a) (hab : a ≤ b) : a.toUInt64 ≤ b.toUInt64 := by
  rw [UInt64.le_iff_toNat_le, toNat_toUInt64_of_le ha, toNat_toUInt64_of_le (Int64.le_trans ha hab)]
  exact Int64.toNatClampNeg_le hab
theorem ISize.toUSize_le {a b : ISize} (ha : 0 ≤ a) (hab : a ≤ b) : a.toUSize ≤ b.toUSize := by
  rw [USize.le_iff_toNat_le, toNat_toUSize_of_le ha, toNat_toUSize_of_le (ISize.le_trans ha hab)]
  exact ISize.toNatClampNeg_le hab

theorem Int8.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 7) : 0 ≤ Int8.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt ha, Int8.toInt_zero]
  exact Int.ofNat_zero_le _
theorem Int16.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 15) : 0 ≤ Int16.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt ha, Int16.toInt_zero]
  exact Int.ofNat_zero_le _
theorem Int32.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 31) : 0 ≤ Int32.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt ha, Int32.toInt_zero]
  exact Int.ofNat_zero_le _
theorem Int64.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ 63) : 0 ≤ Int64.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt ha, Int64.toInt_zero]
  exact Int.ofNat_zero_le _
theorem ISize.zero_le_ofNat_of_lt {a : Nat} (ha : a < 2 ^ (System.Platform.numBits - 1)) :
    0 ≤ ISize.ofNat a := by
  rw [le_iff_toInt_le, toInt_ofNat_of_lt_two_pow_numBits ha, ISize.toInt_zero]
  exact Int.ofNat_zero_le _

protected theorem Int8.sub_nonneg_of_le {a b : Int8} (hb : 0 ≤ b) (hab : b ≤ a) : 0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (Int8.le_trans hb hab),
    ← ofNat_sub _ _ (Int8.toNatClampNeg_le hab)]
  exact Int8.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt)
protected theorem Int16.sub_nonneg_of_le {a b : Int16} (hb : 0 ≤ b) (hab : b ≤ a) : 0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (Int16.le_trans hb hab),
    ← ofNat_sub _ _ (Int16.toNatClampNeg_le hab)]
  exact Int16.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt)
protected theorem Int32.sub_nonneg_of_le {a b : Int32} (hb : 0 ≤ b) (hab : b ≤ a) : 0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (Int32.le_trans hb hab),
    ← ofNat_sub _ _ (Int32.toNatClampNeg_le hab)]
  exact Int32.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt)
protected theorem Int64.sub_nonneg_of_le {a b : Int64} (hb : 0 ≤ b) (hab : b ≤ a) : 0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (Int64.le_trans hb hab),
    ← ofNat_sub _ _ (Int64.toNatClampNeg_le hab)]
  exact Int64.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt)
protected theorem ISize.sub_nonneg_of_le {a b : ISize} (hb : 0 ≤ b) (hab : b ≤ a) : 0 ≤ a - b := by
  rw [← ofNat_toNatClampNeg _ hb, ← ofNat_toNatClampNeg _ (ISize.le_trans hb hab),
    ← ofNat_sub _ _ (ISize.toNatClampNeg_le hab)]
  exact ISize.zero_le_ofNat_of_lt (Nat.sub_lt_of_lt a.toNatClampNeg_lt_two_pow_numBits)

theorem Int8.toNatClampNeg_sub_of_le {a b : Int8} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUInt8_of_le (Int8.sub_nonneg_of_le hb hab), toUInt8_sub,
    UInt8.toNat_sub_of_le _ _ (Int8.toUInt8_le hb hab),
    ← toNat_toUInt8_of_le (Int8.le_trans hb hab), ← toNat_toUInt8_of_le hb]
theorem Int16.toNatClampNeg_sub_of_le {a b : Int16} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUInt16_of_le (Int16.sub_nonneg_of_le hb hab), toUInt16_sub,
    UInt16.toNat_sub_of_le _ _ (Int16.toUInt16_le hb hab),
    ← toNat_toUInt16_of_le (Int16.le_trans hb hab), ← toNat_toUInt16_of_le hb]
theorem Int32.toNatClampNeg_sub_of_le {a b : Int32} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUInt32_of_le (Int32.sub_nonneg_of_le hb hab), toUInt32_sub,
    UInt32.toNat_sub_of_le _ _ (Int32.toUInt32_le hb hab),
    ← toNat_toUInt32_of_le (Int32.le_trans hb hab), ← toNat_toUInt32_of_le hb]
theorem Int64.toNatClampNeg_sub_of_le {a b : Int64} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUInt64_of_le (Int64.sub_nonneg_of_le hb hab), toUInt64_sub,
    UInt64.toNat_sub_of_le _ _ (Int64.toUInt64_le hb hab),
    ← toNat_toUInt64_of_le (Int64.le_trans hb hab), ← toNat_toUInt64_of_le hb]
theorem ISize.toNatClampNeg_sub_of_le {a b : ISize} (hb : 0 ≤ b) (hab : b ≤ a) :
    (a - b).toNatClampNeg = a.toNatClampNeg - b.toNatClampNeg := by
  rw [← toNat_toUSize_of_le (ISize.sub_nonneg_of_le hb hab), toUSize_sub,
    USize.toNat_sub_of_le _ _ (ISize.toUSize_le hb hab),
    ← toNat_toUSize_of_le (ISize.le_trans hb hab), ← toNat_toUSize_of_le hb]

theorem Int8.toInt_sub_of_le (a b : Int8) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int8.toInt_eq_toNatClampNeg (Int8.sub_nonneg_of_le hb h),
    Int8.toInt_eq_toNatClampNeg (Int8.le_trans hb h), Int8.toInt_eq_toNatClampNeg hb,
    Int8.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact Int8.toNatClampNeg_le h
theorem Int16.toInt_sub_of_le (a b : Int16) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int16.toInt_eq_toNatClampNeg (Int16.sub_nonneg_of_le hb h),
    Int16.toInt_eq_toNatClampNeg (Int16.le_trans hb h), Int16.toInt_eq_toNatClampNeg hb,
    Int16.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact Int16.toNatClampNeg_le h
theorem Int32.toInt_sub_of_le (a b : Int32) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_eq_toNatClampNeg (Int32.sub_nonneg_of_le hb h),
    Int32.toInt_eq_toNatClampNeg (Int32.le_trans hb h), Int32.toInt_eq_toNatClampNeg hb,
    Int32.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact Int32.toNatClampNeg_le h
theorem Int64.toInt_sub_of_le (a b : Int64) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int64.toInt_eq_toNatClampNeg (Int64.sub_nonneg_of_le hb h),
    Int64.toInt_eq_toNatClampNeg (Int64.le_trans hb h), Int64.toInt_eq_toNatClampNeg hb,
    Int64.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact Int64.toNatClampNeg_le h
theorem ISize.toInt_sub_of_le (a b : ISize) (hb : 0 ≤ b) (h : b ≤ a) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [ISize.toInt_eq_toNatClampNeg (ISize.sub_nonneg_of_le hb h),
    ISize.toInt_eq_toNatClampNeg (ISize.le_trans hb h), ISize.toInt_eq_toNatClampNeg hb,
    ISize.toNatClampNeg_sub_of_le hb h, Int.ofNat_sub]
  exact ISize.toNatClampNeg_le h

protected theorem Int8.sub_le {a b : Int8} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  simp_all [le_iff_toInt_le, Int8.toInt_sub_of_le _ _ hb hab]; omega
protected theorem Int16.sub_le {a b : Int16} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  simp_all [le_iff_toInt_le, Int16.toInt_sub_of_le _ _ hb hab]; omega
protected theorem Int32.sub_le {a b : Int32} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  simp_all [le_iff_toInt_le, Int32.toInt_sub_of_le _ _ hb hab]; omega
protected theorem Int64.sub_le {a b : Int64} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  simp_all [le_iff_toInt_le, Int64.toInt_sub_of_le _ _ hb hab]; omega
protected theorem ISize.sub_le {a b : ISize} (hb : 0 ≤ b) (hab : b ≤ a) : a - b ≤ a := by
  simp_all [le_iff_toInt_le, ISize.toInt_sub_of_le _ _ hb hab]; omega

protected theorem Int8.sub_lt {a b : Int8} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  simp_all [lt_iff_toInt_lt, Int8.toInt_sub_of_le _ _ (Int8.le_of_lt hb) hab]; omega
protected theorem Int16.sub_lt {a b : Int16} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  simp_all [lt_iff_toInt_lt, Int16.toInt_sub_of_le _ _ (Int16.le_of_lt hb) hab]; omega
protected theorem Int32.sub_lt {a b : Int32} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  simp_all [lt_iff_toInt_lt, Int32.toInt_sub_of_le _ _ (Int32.le_of_lt hb) hab]; omega
protected theorem Int64.sub_lt {a b : Int64} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  simp_all [lt_iff_toInt_lt, Int64.toInt_sub_of_le _ _ (Int64.le_of_lt hb) hab]; omega
protected theorem ISize.sub_lt {a b : ISize} (hb : 0 < b) (hab : b ≤ a) : a - b < a := by
  simp_all [lt_iff_toInt_lt, ISize.toInt_sub_of_le _ _ (ISize.le_of_lt hb) hab]; omega

protected theorem Int8.ne_of_lt {a b : Int8} : a < b → a ≠ b := by
  simpa [Int8.lt_iff_toInt_lt, ← Int8.toInt_inj] using Int.ne_of_lt
protected theorem Int16.ne_of_lt {a b : Int16} : a < b → a ≠ b := by
  simpa [Int16.lt_iff_toInt_lt, ← Int16.toInt_inj] using Int.ne_of_lt
protected theorem Int32.ne_of_lt {a b : Int32} : a < b → a ≠ b := by
  simpa [Int32.lt_iff_toInt_lt, ← Int32.toInt_inj] using Int.ne_of_lt
protected theorem Int64.ne_of_lt {a b : Int64} : a < b → a ≠ b := by
  simpa [Int64.lt_iff_toInt_lt, ← Int64.toInt_inj] using Int.ne_of_lt
protected theorem ISize.ne_of_lt {a b : ISize} : a < b → a ≠ b := by
  simpa [ISize.lt_iff_toInt_lt, ← ISize.toInt_inj] using Int.ne_of_lt

@[simp] theorem Int8.toInt_mod (a b : Int8) : (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, Int8.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int16.toInt_mod (a b : Int16) : (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, Int16.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int32.toInt_mod (a b : Int32) : (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, Int32.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem Int64.toInt_mod (a b : Int64) : (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, Int64.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]
@[simp] theorem ISize.toInt_mod (a b : ISize) : (a % b).toInt = a.toInt.tmod b.toInt := by
  rw [← toInt_toBitVec, ISize.toBitVec_mod, BitVec.toInt_srem, toInt_toBitVec, toInt_toBitVec]

@[simp] theorem Int8.toInt16_mod (a b : Int8) : (a % b).toInt16 = a.toInt16 % b.toInt16 := Int16.toInt.inj (by simp)
@[simp] theorem Int8.toInt32_mod (a b : Int8) : (a % b).toInt32 = a.toInt32 % b.toInt32 := Int32.toInt.inj (by simp)
@[simp] theorem Int8.toInt64_mod (a b : Int8) : (a % b).toInt64 = a.toInt64 % b.toInt64 := Int64.toInt.inj (by simp)
@[simp] theorem Int8.toISize_mod (a b : Int8) : (a % b).toISize = a.toISize % b.toISize := ISize.toInt.inj (by simp)

@[simp] theorem Int16.toInt32_mod (a b : Int16) : (a % b).toInt32 = a.toInt32 % b.toInt32 := Int32.toInt.inj (by simp)
@[simp] theorem Int16.toInt64_mod (a b : Int16) : (a % b).toInt64 = a.toInt64 % b.toInt64 := Int64.toInt.inj (by simp)
@[simp] theorem Int16.toISize_mod (a b : Int16) : (a % b).toISize = a.toISize % b.toISize := ISize.toInt.inj (by simp)

@[simp] theorem Int32.toInt64_mod (a b : Int32) : (a % b).toInt64 = a.toInt64 % b.toInt64 := Int64.toInt.inj (by simp)
@[simp] theorem Int32.toISize_mod (a b : Int32) : (a % b).toISize = a.toISize % b.toISize := ISize.toInt.inj (by simp)

@[simp] theorem ISize.toInt64_mod (a b : ISize) : (a % b).toInt64 = a.toInt64 % b.toInt64 := Int64.toInt.inj (by simp)

theorem Int8.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int8.ofInt (a.tmod b) = Int8.ofInt a % Int8.ofInt b := by
  rw [Int8.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem Int16.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int16.ofInt (a.tmod b) = Int16.ofInt a % Int16.ofInt b := by
  rw [Int16.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem Int32.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int32.ofInt (a.tmod b) = Int32.ofInt a % Int32.ofInt b := by
  rw [Int32.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem Int64.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : Int64.ofInt (a.tmod b) = Int64.ofInt a % Int64.ofInt b := by
  rw [Int64.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact hb₁
  · exact Int.lt_of_le_sub_one hb₂
  · exact ha₁
  · exact Int.lt_of_le_sub_one ha₂
theorem ISize.ofInt_tmod {a b : Int} (ha₁ : minValue.toInt ≤ a) (ha₂ : a ≤ maxValue.toInt)
    (hb₁ : minValue.toInt ≤ b) (hb₂ : b ≤ maxValue.toInt) : ISize.ofInt (a.tmod b) = ISize.ofInt a % ISize.ofInt b := by
  rw [ISize.ofInt_eq_iff_bmod_eq_toInt, ← toInt_bmod_size, toInt_mod, toInt_ofInt, toInt_ofInt,
    Int.bmod_eq_of_le (n := a), Int.bmod_eq_of_le (n := b)]
  · exact le_of_eq_of_le (by cases System.Platform.numBits_eq <;> simp_all [size, toInt_ofInt, toInt_neg]) hb₁
  · refine Int.lt_of_le_sub_one (le_of_le_of_eq hb₂ ?_)
    cases System.Platform.numBits_eq <;> simp_all [size, toInt_ofInt]
  · exact le_of_eq_of_le (by cases System.Platform.numBits_eq <;> simp_all [size, toInt_ofInt, toInt_neg]) ha₁
  · refine Int.lt_of_le_sub_one (le_of_le_of_eq ha₂ ?_)
    cases System.Platform.numBits_eq <;> simp_all [size, toInt_ofInt]

theorem Int8.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int8.ofInt (a.tmod b) = Int8.ofIntLE a ha₁ ha₂ % Int8.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]
theorem Int16.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int16.ofInt (a.tmod b) = Int16.ofIntLE a ha₁ ha₂ % Int16.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]
theorem Int32.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int32.ofInt (a.tmod b) = Int32.ofIntLE a ha₁ ha₂ % Int32.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]
theorem Int64.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    Int64.ofInt (a.tmod b) = Int64.ofIntLE a ha₁ ha₂ % Int64.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]
theorem ISize.ofInt_eq_ofIntLE_mod {a b : Int} (ha₁ ha₂ hb₁ hb₂) :
    ISize.ofInt (a.tmod b) = ISize.ofIntLE a ha₁ ha₂ % ISize.ofIntLE b hb₁ hb₂ := by
  rw [ofIntLE_eq_ofInt, ofIntLE_eq_ofInt, ofInt_tmod ha₁ ha₂ hb₁ hb₂]

theorem Int8.ofNat_mod {a b : Nat} (ha : a < 2 ^ 7) (hb : b < 2 ^ 7) :
    Int8.ofNat (a % b) = Int8.ofNat a % Int8.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod,
    ofInt_tmod (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int16.ofNat_mod {a b : Nat} (ha : a < 2 ^ 15) (hb : b < 2 ^ 15) :
    Int16.ofNat (a % b) = Int16.ofNat a % Int16.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod,
    ofInt_tmod (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int32.ofNat_mod {a b : Nat} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) :
    Int32.ofNat (a % b) = Int32.ofNat a % Int32.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod,
    ofInt_tmod (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem Int64.ofNat_mod {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    Int64.ofNat (a % b) = Int64.ofNat a % Int64.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod,
    ofInt_tmod (by simp) _ (by simp)]
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 hb)
  · exact Int.le_of_lt_add_one (Int.ofNat_le.2 ha)
theorem ISize.ofNat_mod {a b : Nat} (ha : a < 2 ^ (System.Platform.numBits - 1)) (hb : b < 2 ^ (System.Platform.numBits - 1)) :
    ISize.ofNat (a % b) = ISize.ofNat a % ISize.ofNat b := by
  rw [← ofInt_eq_ofNat, ← ofInt_eq_ofNat, ← ofInt_eq_ofNat, Int.ofNat_tmod, ofInt_tmod]
  · exact Int.le_of_lt (Int.lt_of_lt_of_le ISize.toInt_minValue_lt_zero (Int.ofNat_zero_le _))
  · apply Int.le_of_lt_add_one
    simpa only [toInt_maxValue_add_one, ← Int.ofNat_lt, Int.natCast_pow] using ha
  · exact Int.le_of_lt (Int.lt_of_lt_of_le ISize.toInt_minValue_lt_zero (Int.ofNat_zero_le _))
  · apply Int.le_of_lt_add_one
    simpa only [toInt_maxValue_add_one, ← Int.ofNat_lt, Int.natCast_pow] using hb
