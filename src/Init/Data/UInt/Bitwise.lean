/-
Copyright (c) 2024 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Mac Malone
-/
prelude
import Init.Data.UInt.Lemmas
import Init.Data.Fin.Bitwise
import Init.Data.BitVec.Lemmas
import Init.System.Platform

set_option hygiene false in
macro "declare_bitwise_uint_theorems" typeName:ident bits:term:arg : command =>
`(
namespace $typeName

@[simp, int_toBitVec] protected theorem toBitVec_add {a b : $typeName} : (a + b).toBitVec = a.toBitVec + b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_sub {a b : $typeName} : (a - b).toBitVec = a.toBitVec - b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_mul {a b : $typeName} : (a * b).toBitVec = a.toBitVec * b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_div {a b : $typeName} : (a / b).toBitVec = a.toBitVec / b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_mod {a b : $typeName} : (a % b).toBitVec = a.toBitVec % b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_not {a : $typeName} : (~~~a).toBitVec = ~~~a.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_and (a b : $typeName) : (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_or (a b : $typeName) : (a ||| b).toBitVec = a.toBitVec ||| b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_xor (a b : $typeName) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_shiftLeft (a b : $typeName) : (a <<< b).toBitVec = a.toBitVec <<< (b.toBitVec % $bits) := rfl
@[simp, int_toBitVec] protected theorem toBitVec_shiftRight (a b : $typeName) : (a >>> b).toBitVec = a.toBitVec >>> (b.toBitVec % $bits) := rfl

@[simp] protected theorem toNat_and (a b : $typeName) : (a &&& b).toNat = a.toNat &&& b.toNat := by simp [toNat, -toNat_toBitVec]
@[simp] protected theorem toNat_or (a b : $typeName) : (a ||| b).toNat = a.toNat ||| b.toNat := by simp [toNat, -toNat_toBitVec]
@[simp] protected theorem toNat_xor (a b : $typeName) : (a ^^^ b).toNat = a.toNat ^^^ b.toNat := by simp [toNat, -toNat_toBitVec]
@[simp] protected theorem toNat_shiftLeft (a b : $typeName) : (a <<< b).toNat = a.toNat <<< (b.toNat % $bits) % 2 ^ $bits := by simp [toNat, -toNat_toBitVec]
@[simp] protected theorem toNat_shiftRight (a b : $typeName) : (a >>> b).toNat = a.toNat >>> (b.toNat % $bits) := by simp [toNat, -toNat_toBitVec]

open $typeName (toNat_and) in
@[deprecated toNat_and (since := "2024-11-28")]
protected theorem and_toNat (a b : $typeName) : (a &&& b).toNat = a.toNat &&& b.toNat := BitVec.toNat_and ..

end $typeName
)
declare_bitwise_uint_theorems UInt8 8
declare_bitwise_uint_theorems UInt16 16
declare_bitwise_uint_theorems UInt32 32
declare_bitwise_uint_theorems UInt64 64
declare_bitwise_uint_theorems USize System.Platform.numBits

@[simp, int_toBitVec]
theorem Bool.toBitVec_toUInt8 {b : Bool} :
    b.toUInt8.toBitVec = (BitVec.ofBool b).setWidth 8 := by
  cases b <;> simp [toUInt8]

@[simp, int_toBitVec]
theorem Bool.toBitVec_toUInt16 {b : Bool} :
    b.toUInt16.toBitVec = (BitVec.ofBool b).setWidth 16 := by
  cases b <;> simp [toUInt16]

@[simp, int_toBitVec]
theorem Bool.toBitVec_toUInt32 {b : Bool} :
    b.toUInt32.toBitVec = (BitVec.ofBool b).setWidth 32 := by
  cases b <;> simp [toUInt32]

@[simp, int_toBitVec]
theorem Bool.toBitVec_toUInt64 {b : Bool} :
    b.toUInt64.toBitVec = (BitVec.ofBool b).setWidth 64 := by
  cases b <;> simp [toUInt64]

@[simp, int_toBitVec]
theorem Bool.toBitVec_toUSize {b : Bool} :
    b.toUSize.toBitVec = (BitVec.ofBool b).setWidth System.Platform.numBits := by
  cases b
  · simp [toUSize]
  · apply BitVec.eq_of_toNat_eq
    simp [toUSize]

@[simp] theorem UInt8.toFin_and (a b : UInt8) : (a &&& b).toFin = a.toFin &&& b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem UInt16.toFin_and (a b : UInt16) : (a &&& b).toFin = a.toFin &&& b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem UInt32.toFin_and (a b : UInt32) : (a &&& b).toFin = a.toFin &&& b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem UInt64.toFin_and (a b : UInt64) : (a &&& b).toFin = a.toFin &&& b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem USize.toFin_and (a b : USize) : (a &&& b).toFin = a.toFin &&& b.toFin := Fin.val_inj.1 (by simp)

@[simp] theorem UInt8.toUInt16_and (a b : UInt8) : (a &&& b).toUInt16 = a.toUInt16 &&& b.toUInt16 := rfl
@[simp] theorem UInt8.toUInt32_and (a b : UInt8) : (a &&& b).toUInt32 = a.toUInt32 &&& b.toUInt32 := rfl
@[simp] theorem UInt8.toUInt64_and (a b : UInt8) : (a &&& b).toUInt64 = a.toUInt64 &&& b.toUInt64 := rfl
@[simp] theorem UInt8.toUSize_and (a b : UInt8) : (a &&& b).toUSize = a.toUSize &&& b.toUSize := rfl

@[simp] theorem UInt16.toUInt8_and (a b : UInt16) : (a &&& b).toUInt8 = a.toUInt8 &&& b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt16.toUInt32_and (a b : UInt16) : (a &&& b).toUInt32 = a.toUInt32 &&& b.toUInt32 := rfl
@[simp] theorem UInt16.toUInt64_and (a b : UInt16) : (a &&& b).toUInt64 = a.toUInt64 &&& b.toUInt64 := rfl
@[simp] theorem UInt16.toUSize_and (a b : UInt16) : (a &&& b).toUSize = a.toUSize &&& b.toUSize := rfl

@[simp] theorem UInt32.toUInt8_and (a b : UInt32) : (a &&& b).toUInt8 = a.toUInt8 &&& b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.toUInt16_and (a b : UInt32) : (a &&& b).toUInt16 = a.toUInt16 &&& b.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.toUInt64_and (a b : UInt32) : (a &&& b).toUInt64 = a.toUInt64 &&& b.toUInt64 := rfl
@[simp] theorem UInt32.toUSize_and (a b : UInt32) : (a &&& b).toUSize = a.toUSize &&& b.toUSize := rfl

@[simp] theorem USize.toUInt8_and (a b : USize) : (a &&& b).toUInt8 = a.toUInt8 &&& b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt16_and (a b : USize) : (a &&& b).toUInt16 = a.toUInt16 &&& b.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt32_and (a b : USize) : (a &&& b).toUInt32 = a.toUInt32 &&& b.toUInt32 := UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt64_and (a b : USize) : (a &&& b).toUInt64 = a.toUInt64 &&& b.toUInt64 := rfl

@[simp] theorem UInt64.toUInt8_and (a b : UInt64) : (a &&& b).toUInt8 = a.toUInt8 &&& b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt16_and (a b : UInt64) : (a &&& b).toUInt16 = a.toUInt16 &&& b.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt32_and (a b : UInt64) : (a &&& b).toUInt32 = a.toUInt32 &&& b.toUInt32 := UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUSize_and (a b : UInt64) : (a &&& b).toUSize = a.toUSize &&& b.toUSize := USize.toBitVec_inj.1 (by simp)

@[simp] theorem UInt8.toFin_or (a b : UInt8) : (a ||| b).toFin = a.toFin ||| b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem UInt16.toFin_or (a b : UInt16) : (a ||| b).toFin = a.toFin ||| b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem UInt32.toFin_or (a b : UInt32) : (a ||| b).toFin = a.toFin ||| b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem UInt64.toFin_or (a b : UInt64) : (a ||| b).toFin = a.toFin ||| b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem USize.toFin_or (a b : USize) : (a ||| b).toFin = a.toFin ||| b.toFin := Fin.val_inj.1 (by simp)

@[simp] theorem UInt8.toUInt16_or (a b : UInt8) : (a ||| b).toUInt16 = a.toUInt16 ||| b.toUInt16 := rfl
@[simp] theorem UInt8.toUInt32_or (a b : UInt8) : (a ||| b).toUInt32 = a.toUInt32 ||| b.toUInt32 := rfl
@[simp] theorem UInt8.toUInt64_or (a b : UInt8) : (a ||| b).toUInt64 = a.toUInt64 ||| b.toUInt64 := rfl
@[simp] theorem UInt8.toUSize_or (a b : UInt8) : (a ||| b).toUSize = a.toUSize ||| b.toUSize := rfl

@[simp] theorem UInt16.toUInt8_or (a b : UInt16) : (a ||| b).toUInt8 = a.toUInt8 ||| b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt16.toUInt32_or (a b : UInt16) : (a ||| b).toUInt32 = a.toUInt32 ||| b.toUInt32 := rfl
@[simp] theorem UInt16.toUInt64_or (a b : UInt16) : (a ||| b).toUInt64 = a.toUInt64 ||| b.toUInt64 := rfl
@[simp] theorem UInt16.toUSize_or (a b : UInt16) : (a ||| b).toUSize = a.toUSize ||| b.toUSize := rfl

@[simp] theorem UInt32.toUInt8_or (a b : UInt32) : (a ||| b).toUInt8 = a.toUInt8 ||| b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.toUInt16_or (a b : UInt32) : (a ||| b).toUInt16 = a.toUInt16 ||| b.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.toUInt64_or (a b : UInt32) : (a ||| b).toUInt64 = a.toUInt64 ||| b.toUInt64 := rfl
@[simp] theorem UInt32.toUSize_or (a b : UInt32) : (a ||| b).toUSize = a.toUSize ||| b.toUSize := rfl

@[simp] theorem USize.toUInt8_or (a b : USize) : (a ||| b).toUInt8 = a.toUInt8 ||| b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt16_or (a b : USize) : (a ||| b).toUInt16 = a.toUInt16 ||| b.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt32_or (a b : USize) : (a ||| b).toUInt32 = a.toUInt32 ||| b.toUInt32 := UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt64_or (a b : USize) : (a ||| b).toUInt64 = a.toUInt64 ||| b.toUInt64 := rfl

@[simp] theorem UInt64.toUInt8_or (a b : UInt64) : (a ||| b).toUInt8 = a.toUInt8 ||| b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt16_or (a b : UInt64) : (a ||| b).toUInt16 = a.toUInt16 ||| b.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt32_or (a b : UInt64) : (a ||| b).toUInt32 = a.toUInt32 ||| b.toUInt32 := UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUSize_or (a b : UInt64) : (a ||| b).toUSize = a.toUSize ||| b.toUSize := USize.toBitVec_inj.1 (by simp)

@[simp] theorem UInt8.toFin_xor (a b : UInt8) : (a ^^^ b).toFin = a.toFin ^^^ b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem UInt16.toFin_xor (a b : UInt16) : (a ^^^ b).toFin = a.toFin ^^^ b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem UInt32.toFin_xor (a b : UInt32) : (a ^^^ b).toFin = a.toFin ^^^ b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem UInt64.toFin_xor (a b : UInt64) : (a ^^^ b).toFin = a.toFin ^^^ b.toFin := Fin.val_inj.1 (by simp)
@[simp] theorem USize.toFin_xor (a b : USize) : (a ^^^ b).toFin = a.toFin ^^^ b.toFin := Fin.val_inj.1 (by simp)

@[simp] theorem UInt8.toUInt16_xor (a b : UInt8) : (a ^^^ b).toUInt16 = a.toUInt16 ^^^ b.toUInt16 := rfl
@[simp] theorem UInt8.toUInt32_xor (a b : UInt8) : (a ^^^ b).toUInt32 = a.toUInt32 ^^^ b.toUInt32 := rfl
@[simp] theorem UInt8.toUInt64_xor (a b : UInt8) : (a ^^^ b).toUInt64 = a.toUInt64 ^^^ b.toUInt64 := rfl
@[simp] theorem UInt8.toUSize_xor (a b : UInt8) : (a ^^^ b).toUSize = a.toUSize ^^^ b.toUSize := rfl

@[simp] theorem UInt16.toUInt8_xor (a b : UInt16) : (a ^^^ b).toUInt8 = a.toUInt8 ^^^ b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt16.toUInt32_xor (a b : UInt16) : (a ^^^ b).toUInt32 = a.toUInt32 ^^^ b.toUInt32 := rfl
@[simp] theorem UInt16.toUInt64_xor (a b : UInt16) : (a ^^^ b).toUInt64 = a.toUInt64 ^^^ b.toUInt64 := rfl
@[simp] theorem UInt16.toUSize_xor (a b : UInt16) : (a ^^^ b).toUSize = a.toUSize ^^^ b.toUSize := rfl

@[simp] theorem UInt32.toUInt8_xor (a b : UInt32) : (a ^^^ b).toUInt8 = a.toUInt8 ^^^ b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.toUInt16_xor (a b : UInt32) : (a ^^^ b).toUInt16 = a.toUInt16 ^^^ b.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.toUInt64_xor (a b : UInt32) : (a ^^^ b).toUInt64 = a.toUInt64 ^^^ b.toUInt64 := rfl
@[simp] theorem UInt32.toUSize_xor (a b : UInt32) : (a ^^^ b).toUSize = a.toUSize ^^^ b.toUSize := rfl

@[simp] theorem USize.toUInt8_xor (a b : USize) : (a ^^^ b).toUInt8 = a.toUInt8 ^^^ b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt16_xor (a b : USize) : (a ^^^ b).toUInt16 = a.toUInt16 ^^^ b.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt32_xor (a b : USize) : (a ^^^ b).toUInt32 = a.toUInt32 ^^^ b.toUInt32 := UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt64_xor (a b : USize) : (a ^^^ b).toUInt64 = a.toUInt64 ^^^ b.toUInt64 := rfl

@[simp] theorem UInt64.toUInt8_xor (a b : UInt64) : (a ^^^ b).toUInt8 = a.toUInt8 ^^^ b.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt16_xor (a b : UInt64) : (a ^^^ b).toUInt16 = a.toUInt16 ^^^ b.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt32_xor (a b : UInt64) : (a ^^^ b).toUInt32 = a.toUInt32 ^^^ b.toUInt32 := UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUSize_xor (a b : UInt64) : (a ^^^ b).toUSize = a.toUSize ^^^ b.toUSize := USize.toBitVec_inj.1 (by simp)

@[simp] theorem UInt8.toNat_not (a : UInt8) : (~~~a).toNat = UInt8.size - 1 - a.toNat := by
  rw [← toNat_toBitVec, UInt8.toBitVec_not, BitVec.toNat_not, toNat_toBitVec]
@[simp] theorem UInt16.toNat_not (a : UInt16) : (~~~a).toNat = UInt16.size - 1 - a.toNat := by
  rw [← toNat_toBitVec, UInt16.toBitVec_not, BitVec.toNat_not, toNat_toBitVec]
@[simp] theorem UInt32.toNat_not (a : UInt32) : (~~~a).toNat = UInt32.size - 1 - a.toNat := by
  rw [← toNat_toBitVec, UInt32.toBitVec_not, BitVec.toNat_not, toNat_toBitVec]
@[simp] theorem UInt64.toNat_not (a : UInt64) : (~~~a).toNat = UInt64.size - 1 - a.toNat := by
  rw [← toNat_toBitVec, UInt64.toBitVec_not, BitVec.toNat_not, toNat_toBitVec]
@[simp] theorem USize.toNat_not (a : USize) : (~~~a).toNat = USize.size - 1 - a.toNat := by
  rw [← toNat_toBitVec, USize.toBitVec_not, BitVec.toNat_not, toNat_toBitVec]

@[simp] theorem UInt8.toFin_not (a : UInt8) : (~~~a).toFin = a.toFin.rev := by
  rw [← toFin_toBitVec, UInt8.toBitVec_not, BitVec.toFin_not, toFin_toBitVec]
@[simp] theorem UInt16.toFin_not (a : UInt16) : (~~~a).toFin = a.toFin.rev := by
  rw [← toFin_toBitVec, UInt16.toBitVec_not, BitVec.toFin_not, toFin_toBitVec]
@[simp] theorem UInt32.toFin_not (a : UInt32) : (~~~a).toFin = a.toFin.rev := by
  rw [← toFin_toBitVec, UInt32.toBitVec_not, BitVec.toFin_not, toFin_toBitVec]
@[simp] theorem UInt64.toFin_not (a : UInt64) : (~~~a).toFin = a.toFin.rev := by
  rw [← toFin_toBitVec, UInt64.toBitVec_not, BitVec.toFin_not, toFin_toBitVec]
@[simp] theorem USize.toFin_not (a : USize) : (~~~a).toFin = a.toFin.rev := by
  rw [← toFin_toBitVec, USize.toBitVec_not, BitVec.toFin_not, toFin_toBitVec]

@[simp] theorem System.Platform.eight_le_numBits : 8 ≤ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp_all
@[simp] theorem System.Platform.sixteen_le_numBits : 16 ≤ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem System.Platform.eight_dvd_numBits : 8 ∣ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp_all
@[simp] theorem System.Platform.sixteen_dvd_numBits : 16 ∣ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp_all
@[simp] theorem System.Platform.dvd_numBits : 32 ∣ System.Platform.numBits := by
  cases System.Platform.numBits_eq <;> simp_all
@[simp] theorem System.Platform.numBits_dvd : System.Platform.numBits ∣ 64 := by
  cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem UInt16.toUInt8_not (a : UInt16) : (~~~a).toUInt8 = ~~~a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.toUInt8_not (a : UInt32) : (~~~a).toUInt8 = ~~~a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt8_not (a : UInt64) : (~~~a).toUInt8 = ~~~a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt8_not (a : USize) : (~~~a).toUInt8 = ~~~a.toUInt8 := UInt8.toBitVec_inj.1 (by simp)

@[simp] theorem UInt32.toUInt16_not (a : UInt32) : (~~~a).toUInt16 = ~~~a.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.toUInt16_not (a : UInt64) : (~~~a).toUInt16 = ~~~a.toUInt16 := UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt16_not (a : USize) : (~~~a).toUInt16 = ~~~a.toUInt16 := UInt16.toBitVec_inj.1 (by simp)

@[simp] theorem UInt64.toUInt32_not (a : UInt64) : (~~~a).toUInt32 = ~~~a.toUInt32 := UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem USize.toUInt32_not (a : USize) : (~~~a).toUInt32 = ~~~a.toUInt32 := UInt32.toBitVec_inj.1 (by simp)

@[simp] theorem UInt64.toUSize_not (a : UInt64) : (~~~a).toUSize = ~~~a.toUSize := USize.toBitVec_inj.1 (by simp)

@[simp] theorem UInt8.toUInt16_not (a : UInt8) : (~~~a).toUInt16 = ~~~a.toUInt16 % 256 := by
  simp [UInt8.toUInt16_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt32_not (a : UInt8) : (~~~a).toUInt32 = ~~~a.toUInt32 % 256 := by
  simp [UInt8.toUInt32_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt64_not (a : UInt8) : (~~~a).toUInt64 = ~~~a.toUInt64 % 256 := by
  simp [UInt8.toUInt64_eq_mod_256_iff]
@[simp] theorem UInt8.toUSize_not (a : UInt8) : (~~~a).toUSize = ~~~a.toUSize % 256 := by
  simp [UInt8.toUSize_eq_mod_256_iff]

@[simp] theorem UInt16.toUInt32_not (a : UInt16) : (~~~a).toUInt32 = ~~~a.toUInt32 % 65536 := by
  simp [UInt16.toUInt32_eq_mod_65536_iff]
@[simp] theorem UInt16.toUInt64_not (a : UInt16) : (~~~a).toUInt64 = ~~~a.toUInt64 % 65536 := by
  simp [UInt16.toUInt64_eq_mod_65536_iff]
@[simp] theorem UInt16.toUSize_not (a : UInt16) : (~~~a).toUSize = ~~~a.toUSize % 65536 := by
  simp [UInt16.toUSize_eq_mod_65536_iff]

@[simp] theorem UInt32.toUInt64_not (a : UInt32) : (~~~a).toUInt64 = ~~~a.toUInt64 % 4294967296 := by
  simp [UInt32.toUInt64_eq_mod_4294967296_iff]
@[simp] theorem UInt32.toUSize_not (a : UInt32) : (~~~a).toUSize = ~~~a.toUSize % 4294967296 := by
  simp [UInt32.toUSize_eq_mod_4294967296_iff]

@[simp] theorem USize.toUInt64_not (a : USize) : (~~~a).toUInt64 = ~~~a.toUInt64 % UInt64.ofNat USize.size := by
  simp [USize.toUInt64_eq_mod_usizeSize_iff]

@[simp] theorem UInt8.toFin_shiftLeft (a b : UInt8) (hb : b < 8) : (a <<< b).toFin = a.toFin <<< b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := 8) hb])
@[simp] theorem UInt16.toFin_shiftLeft (a b : UInt16) (hb : b < 16) : (a <<< b).toFin = a.toFin <<< b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := 16) hb])
@[simp] theorem UInt32.toFin_shiftLeft (a b : UInt32) (hb : b < 32) : (a <<< b).toFin = a.toFin <<< b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := 32) hb])
@[simp] theorem UInt64.toFin_shiftLeft (a b : UInt64) (hb : b < 64) : (a <<< b).toFin = a.toFin <<< b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := 64) hb])
@[simp] theorem USize.toFin_shiftLeft (a b : USize) (hb : b.toNat < System.Platform.numBits) : (a <<< b).toFin = a.toFin <<< b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := System.Platform.numBits) hb])

@[simp] theorem BitVec.setWidth_shiftLeft_of_le (hi : i ≤ v) (a : BitVec v) (b : Nat) :
    (a <<< b).setWidth i = a.setWidth i <<< b :=
  eq_of_getElem_eq (fun j hj => Bool.eq_iff_iff.2 (by simp; omega))

@[simp] theorem BitVec.setWidth_shiftRight (hi : v ≤ i) (a : BitVec v) (b : Nat):
    (a >>> b).setWidth i = a.setWidth i >>> b := by
  refine eq_of_getElem_eq (fun j hj => ?_)
  simp only [getElem_setWidth, getLsbD_ushiftRight, getElem_ushiftRight, getLsbD_setWidth,
    Bool.iff_and_self, decide_eq_true_eq]
  intro ha
  have := lt_of_getLsbD ha
  omega


theorem UInt8.shiftLeft_eq_shiftLeft_mod (a b : UInt8) : a <<< b = a <<< (b % 8) := UInt8.toBitVec_inj.1 (by simp)
theorem UInt16.shiftLeft_eq_shiftLeft_mod (a b : UInt16) : a <<< b = a <<< (b % 16) := UInt16.toBitVec_inj.1 (by simp)
theorem UInt32.shiftLeft_eq_shiftLeft_mod (a b : UInt32) : a <<< b = a <<< (b % 32) := UInt32.toBitVec_inj.1 (by simp)
theorem UInt64.shiftLeft_eq_shiftLeft_mod (a b : UInt64) : a <<< b = a <<< (b % 64) := UInt64.toBitVec_inj.1 (by simp)
theorem USize.shiftLeft_eq_shiftLeft_mod (a b : USize) : a <<< b = a <<< (b % USize.ofNat System.Platform.numBits) :=
  USize.toBitVec_inj.1 (by simp)

theorem UInt8.shiftRight_eq_shiftRight_mod (a b : UInt8) : a >>> b = a >>> (b % 8) := UInt8.toBitVec_inj.1 (by simp)
theorem UInt16.shiftRight_eq_shiftRight_mod (a b : UInt16) : a >>> b = a >>> (b % 16) := UInt16.toBitVec_inj.1 (by simp)
theorem UInt32.shiftRight_eq_shiftRight_mod (a b : UInt32) : a >>> b = a >>> (b % 32) := UInt32.toBitVec_inj.1 (by simp)
theorem UInt64.shiftRight_eq_shiftRight_mod (a b : UInt64) : a >>> b = a >>> (b % 64) := UInt64.toBitVec_inj.1 (by simp)
theorem USize.shiftRight_eq_shiftRight_mod (a b : USize) : a >>> b = a >>> (b % USize.ofNat System.Platform.numBits) :=
  USize.toBitVec_inj.1 (by simp)

@[simp] theorem UInt16.toUInt8_shiftLeft (a b : UInt16) (hb : b < 8) : (a <<< b).toUInt8 = a.toUInt8 <<< b.toUInt8 := by
  apply UInt8.toBitVec_inj.1
  simp only [lt_iff_toNat_lt, UInt16.reduceToNat] at hb
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_trans hb (by decide : 8 < 16))]

@[simp] theorem UInt32.toUInt8_shiftLeft (a b : UInt32) (hb : b < 8) : (a <<< b).toUInt8 = a.toUInt8 <<< b.toUInt8 := by
  apply UInt8.toBitVec_inj.1
  simp only [lt_iff_toNat_lt, UInt32.reduceToNat] at hb
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_trans hb (by decide : 8 < 32))]
@[simp] theorem UInt32.toUInt16_shiftLeft (a b : UInt32) (hb : b < 16) : (a <<< b).toUInt16 = a.toUInt16 <<< b.toUInt16 := by
  apply UInt16.toBitVec_inj.1
  simp only [lt_iff_toNat_lt, UInt32.reduceToNat] at hb
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_trans hb (by decide : 16 < 32))]

@[simp] theorem USize.toUInt8_shiftLeft (a b : USize) (hb : b < 8) : (a <<< b).toUInt8 = a.toUInt8 <<< b.toUInt8 := by
  apply UInt8.toBitVec_inj.1
  simp only [lt_iff_toNat_lt, USize.reduceToNat] at hb
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb System.Platform.eight_le_numBits)]
@[simp] theorem USize.toUInt16_shiftLeft (a b : USize) (hb : b < 16) : (a <<< b).toUInt16 = a.toUInt16 <<< b.toUInt16 := by
  apply UInt16.toBitVec_inj.1
  simp only [lt_iff_toNat_lt, USize.reduceToNat] at hb
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb System.Platform.sixteen_le_numBits)]
@[simp] theorem USize.toUInt32_shiftLeft (a b : USize) (hb : b < 32) : (a <<< b).toUInt32 = a.toUInt32 <<< b.toUInt32 := by
  apply UInt32.toBitVec_inj.1
  simp only [lt_iff_toNat_lt, USize.reduceToNat] at hb
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb System.Platform.le_numBits)]

@[simp] theorem UInt64.toUInt8_shiftLeft (a b : UInt64) (hb : b < 8) : (a <<< b).toUInt8 = a.toUInt8 <<< b.toUInt8 := by
  apply UInt8.toBitVec_inj.1
  simp only [lt_iff_toNat_lt, UInt64.reduceToNat] at hb
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb (by decide : 8 ≤ 64))]
@[simp] theorem UInt64.toUInt16_shiftLeft (a b : UInt64) (hb : b < 16) : (a <<< b).toUInt16 = a.toUInt16 <<< b.toUInt16 := by
  apply UInt16.toBitVec_inj.1
  simp only [lt_iff_toNat_lt, UInt64.reduceToNat] at hb
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb (by decide : 16 ≤ 64))]
@[simp] theorem UInt64.toUInt32_shiftLeft (a b : UInt64) (hb : b < 32) : (a <<< b).toUInt32 = a.toUInt32 <<< b.toUInt32 := by
  apply UInt32.toBitVec_inj.1
  simp only [lt_iff_toNat_lt, UInt64.reduceToNat] at hb
  simp [Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb (by decide : 32 ≤ 64))]
@[simp] theorem UInt64.toUSize_shiftLeft (a b : UInt64) (hb : b.toNat < System.Platform.numBits) :
    (a <<< b).toUSize = a.toUSize <<< b.toUSize := by
  apply USize.toBitVec_inj.1
  have h₁ : b.toNat % 64 = b.toNat := Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hb System.Platform.numBits_le)
  have h₂ : b.toNat % (2 ^ System.Platform.numBits) % System.Platform.numBits = b.toNat := by
    rw [Nat.mod_eq_of_lt (a := b.toNat), Nat.mod_eq_of_lt hb]
    exact Nat.lt_trans hb (Nat.lt_pow_self Nat.one_lt_two)
  simp [h₁, h₂]

@[simp] theorem UInt16.toUInt8_shiftLeft_mod (a b : UInt16) : (a <<< (b % 8)).toUInt8 = a.toUInt8 <<< b.toUInt8 := by
  rw [UInt16.toUInt8_shiftLeft _ _ (Nat.mod_lt _ (by decide)), UInt16.toUInt8_mod_of_dvd _ _ (by simp)]
  simp [← UInt8.shiftLeft_eq_shiftLeft_mod]

@[simp] theorem UInt32.toUInt8_shiftLeft_mod (a b : UInt32) : (a <<< (b % 8)).toUInt8 = a.toUInt8 <<< b.toUInt8 := by
  rw [UInt32.toUInt8_shiftLeft _ _ (Nat.mod_lt _ (by decide)), UInt32.toUInt8_mod_of_dvd _ _ (by simp)]
  simp [← UInt8.shiftLeft_eq_shiftLeft_mod]
@[simp] theorem UInt32.toUInt16_shiftLeft_mod (a b : UInt32) : (a <<< (b % 16)).toUInt16 = a.toUInt16 <<< b.toUInt16 := by
  rw [UInt32.toUInt16_shiftLeft _ _ (Nat.mod_lt _ (by decide)), UInt32.toUInt16_mod_of_dvd _ _ (by simp)]
  simp [← UInt16.shiftLeft_eq_shiftLeft_mod]

@[simp] theorem USize.toUInt8_shiftLeft_mod (a b : USize) : (a <<< (b % 8)).toUInt8 = a.toUInt8 <<< b.toUInt8 := by
  rw [USize.toUInt8_shiftLeft _ _ (Nat.mod_lt _ (by simp [-toBitVec_ofNat])), USize.toUInt8_mod_of_dvd _ _ (by simp)]
  simp [← UInt8.shiftLeft_eq_shiftLeft_mod]
@[simp] theorem USize.toUInt16_shiftLeft_mod (a b : USize) : (a <<< (b % 16)).toUInt16 = a.toUInt16 <<< b.toUInt16 := by
  rw [USize.toUInt16_shiftLeft _ _ (Nat.mod_lt _ (by simp [-toBitVec_ofNat])), USize.toUInt16_mod_of_dvd _ _ (by simp)]
  simp [← UInt16.shiftLeft_eq_shiftLeft_mod]
@[simp] theorem USize.toUInt32_shiftLeft_mod (a b : USize) : (a <<< (b % 32)).toUInt32 = a.toUInt32 <<< b.toUInt32 := by
  rw [USize.toUInt32_shiftLeft _ _ (Nat.mod_lt _ (by simp [-toBitVec_ofNat])), USize.toUInt32_mod_of_dvd _ _ (by simp)]
  simp [← UInt32.shiftLeft_eq_shiftLeft_mod]

@[simp] theorem UInt64.toUInt8_shiftLeft_mod (a b : UInt64) : (a <<< (b % 8)).toUInt8 = a.toUInt8 <<< b.toUInt8 := by
  rw [UInt64.toUInt8_shiftLeft _ _ (Nat.mod_lt _ (by decide)), UInt64.toUInt8_mod_of_dvd _ _ (by simp)]
  simp [← UInt8.shiftLeft_eq_shiftLeft_mod]
@[simp] theorem UInt64.toUInt16_shiftLeft_mod (a b : UInt64) : (a <<< (b % 16)).toUInt16 = a.toUInt16 <<< b.toUInt16 := by
  rw [UInt64.toUInt16_shiftLeft _ _ (Nat.mod_lt _ (by decide)), UInt64.toUInt16_mod_of_dvd _ _ (by simp)]
  simp [← UInt16.shiftLeft_eq_shiftLeft_mod]
@[simp] theorem UInt64.toUInt32_shiftLeft_mod (a b : UInt64) : (a <<< (b % 32)).toUInt32 = a.toUInt32 <<< b.toUInt32 := by
  rw [UInt64.toUInt32_shiftLeft _ _ (Nat.mod_lt _ (by decide)), UInt64.toUInt32_mod_of_dvd _ _ (by simp)]
  simp [← UInt32.shiftLeft_eq_shiftLeft_mod]
@[simp] theorem UInt64.toUSize_shiftLeft_mod (a b : UInt64) : (a <<< (b % UInt64.ofNat System.Platform.numBits)).toUSize = a.toUSize <<< b.toUSize := by
  rw [UInt64.toUSize_shiftLeft, UInt64.toUSize_mod_of_dvd]
  · simp [← USize.shiftLeft_eq_shiftLeft_mod]
  · cases System.Platform.numBits_eq <;> simp_all
  · cases System.Platform.numBits_eq <;> simp_all [Nat.mod_lt]

@[simp] theorem UInt8.toUInt16_lt {a b : UInt8} : a.toUInt16 < b.toUInt16 ↔ a < b := Iff.rfl
@[simp] theorem UInt8.toUInt32_lt {a b : UInt8} : a.toUInt32 < b.toUInt32 ↔ a < b := Iff.rfl
@[simp] theorem UInt8.toUInt64_lt {a b : UInt8} : a.toUInt64 < b.toUInt64 ↔ a < b := Iff.rfl
@[simp] theorem UInt8.toUSize_lt {a b : UInt8} : a.toUSize < b.toUSize ↔ a < b := Iff.rfl

theorem UInt8.toUInt16_shiftLeft_of_lt (a b : UInt8) (hb : b < 8) : (a <<< b).toUInt16 = (a.toUInt16 <<< b.toUInt16) % 256 := by
  rwa [UInt8.toUInt16_eq_mod_256_iff, UInt16.toUInt8_shiftLeft, toUInt8_toUInt16, toUInt8_toUInt16]
theorem UInt8.toUInt32_shiftLeft_of_lt (a b : UInt8) (hb : b < 8) : (a <<< b).toUInt32 = (a.toUInt32 <<< b.toUInt32) % 256 := by
  rwa [UInt8.toUInt32_eq_mod_256_iff, UInt32.toUInt8_shiftLeft, toUInt8_toUInt32, toUInt8_toUInt32]
theorem UInt8.toUInt64_shiftLeft_of_lt (a b : UInt8) (hb : b < 8) : (a <<< b).toUInt64 = (a.toUInt64 <<< b.toUInt64) % 256 := by
  rwa [UInt8.toUInt64_eq_mod_256_iff, UInt64.toUInt8_shiftLeft, toUInt8_toUInt64, toUInt8_toUInt64]
theorem UInt8.toUSize_shiftLeft_of_lt (a b : UInt8) (hb : b < 8) : (a <<< b).toUSize = (a.toUSize <<< b.toUSize) % 256 := by
  rw [UInt8.toUSize_eq_mod_256_iff, USize.toUInt8_shiftLeft, toUInt8_toUSize, toUInt8_toUSize]
  simpa [USize.lt_iff_toNat_lt]

theorem UInt16.toUInt32_shiftLeft_of_lt (a b : UInt16) (hb : b < 16) : (a <<< b).toUInt32 = (a.toUInt32 <<< b.toUInt32) % 65536 := by
  rwa [UInt16.toUInt32_eq_mod_65536_iff, UInt32.toUInt16_shiftLeft, toUInt16_toUInt32, toUInt16_toUInt32]
theorem UInt16.toUInt64_shiftLeft_of_lt (a b : UInt16) (hb : b < 16) : (a <<< b).toUInt64 = (a.toUInt64 <<< b.toUInt64) % 65536 := by
  rwa [UInt16.toUInt64_eq_mod_65536_iff, UInt64.toUInt16_shiftLeft, toUInt16_toUInt64, toUInt16_toUInt64]
theorem UInt16.toUSize_shiftLeft_of_lt (a b : UInt16) (hb : b < 16) : (a <<< b).toUSize = (a.toUSize <<< b.toUSize) % 65536 := by
  rw [UInt16.toUSize_eq_mod_65536_iff, USize.toUInt16_shiftLeft, toUInt16_toUSize, toUInt16_toUSize]
  simpa [USize.lt_iff_toNat_lt]

theorem UInt32.toUInt64_shiftLeft_of_lt (a b : UInt32) (hb : b < 32) : (a <<< b).toUInt64 = (a.toUInt64 <<< b.toUInt64) % 4294967296 := by
  rwa [UInt32.toUInt64_eq_mod_4294967296_iff, UInt64.toUInt32_shiftLeft, toUInt32_toUInt64, toUInt32_toUInt64]
theorem UInt32.toUSize_shiftLeft_of_lt (a b : UInt32) (hb : b < 32) : (a <<< b).toUSize = (a.toUSize <<< b.toUSize) % 4294967296 := by
  rw [UInt32.toUSize_eq_mod_4294967296_iff, USize.toUInt32_shiftLeft, toUInt32_toUSize, toUInt32_toUSize]
  simpa [USize.lt_iff_toNat_lt]

theorem USize.toUInt64_shiftLeft_of_lt (a b : USize) (hb : b.toNat < System.Platform.numBits) : (a <<< b).toUInt64 = (a.toUInt64 <<< b.toUInt64) % UInt64.ofNat USize.size := by
  rwa [USize.toUInt64_eq_mod_usizeSize_iff, UInt64.toUSize_shiftLeft, toUSize_toUInt64, toUSize_toUInt64]

@[simp] theorem UInt8.toUInt16_shiftLeft (a b : UInt8) : (a <<< b).toUInt16 = (a.toUInt16 <<< (b % 8).toUInt16) % 256 := by
  simp [UInt8.toUInt16_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt32_shiftLeft (a b : UInt8) : (a <<< b).toUInt32 = (a.toUInt32 <<< (b % 8).toUInt32) % 256 := by
  simp [UInt8.toUInt32_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt64_shiftLeft (a b : UInt8) : (a <<< b).toUInt64 = (a.toUInt64 <<< (b % 8).toUInt64) % 256 := by
  simp [UInt8.toUInt64_eq_mod_256_iff]
@[simp] theorem UInt8.toUSize_shiftLeft (a b : UInt8) : (a <<< b).toUSize = (a.toUSize <<< (b % 8).toUSize) % 256 := by
  simp [UInt8.toUSize_eq_mod_256_iff]

@[simp] theorem UInt16.toUInt32_shiftLeft (a b : UInt16) : (a <<< b).toUInt32 = (a.toUInt32 <<< (b % 16).toUInt32) % 65536 := by
  simp [UInt16.toUInt32_eq_mod_65536_iff]
@[simp] theorem UInt16.toUInt64_shiftLeft (a b : UInt16) : (a <<< b).toUInt64 = (a.toUInt64 <<< (b % 16).toUInt64) % 65536 := by
  simp [UInt16.toUInt64_eq_mod_65536_iff]
@[simp] theorem UInt16.toUSize_shiftLeft (a b : UInt16) : (a <<< b).toUSize = (a.toUSize <<< (b % 16).toUSize) % 65536 := by
  simp [UInt16.toUSize_eq_mod_65536_iff]

@[simp] theorem UInt32.toUInt64_shiftLeft (a b : UInt32) : (a <<< b).toUInt64 = (a.toUInt64 <<< (b % 32).toUInt64) % 4294967296 := by
  simp [UInt32.toUInt64_eq_mod_4294967296_iff]
@[simp] theorem UInt32.toUSize_shiftLeft (a b : UInt32) : (a <<< b).toUSize = (a.toUSize <<< (b % 32).toUSize) % 4294967296 := by
  simp [UInt32.toUSize_eq_mod_4294967296_iff]

@[simp] theorem USize.toUInt64_shiftLeft (a b : USize) :
    (a <<< b).toUInt64 = (a.toUInt64 <<< (b % USize.ofNat System.Platform.numBits).toUInt64) % UInt64.ofNat USize.size := by
  have : System.Platform.numBits < USize.size := Nat.lt_of_le_of_lt System.Platform.numBits_le (Nat.lt_of_lt_of_le (by decide) USize.le_size)
  simp [USize.toUInt64_eq_mod_usizeSize_iff, toUInt64_ofNat' this]

@[simp] theorem UInt8.toFin_shiftRight (a b : UInt8) (hb : b < 8) : (a >>> b).toFin = a.toFin >>> b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := 8) hb])
@[simp] theorem UInt16.toFin_shiftRight (a b : UInt16) (hb : b < 16) : (a >>> b).toFin = a.toFin >>> b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := 16) hb])
@[simp] theorem UInt32.toFin_shiftRight (a b : UInt32) (hb : b < 32) : (a >>> b).toFin = a.toFin >>> b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := 32) hb])
@[simp] theorem UInt64.toFin_shiftRight (a b : UInt64) (hb : b < 64) : (a >>> b).toFin = a.toFin >>> b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := 64) hb])
@[simp] theorem USize.toFin_shiftRight (a b : USize) (hb : b.toNat < System.Platform.numBits) : (a >>> b).toFin = a.toFin >>> b.toFin :=
  Fin.val_inj.1 (by simp [Nat.mod_eq_of_lt (a := b.toNat) (b := System.Platform.numBits) hb])

@[simp] theorem UInt8.toUInt16_shiftRight (a b : UInt8) : (a >>> b).toUInt16 = a.toUInt16 >>> (b.toUInt16 % 8) :=
  UInt16.toBitVec_inj.1 (by simp [Nat.mod_mod_of_dvd' (by decide : 8 ∣ 16)])
@[simp] theorem UInt8.toUInt32_shiftRight (a b : UInt8) : (a >>> b).toUInt32 = a.toUInt32 >>> (b.toUInt32 % 8) :=
  UInt32.toBitVec_inj.1 (by simp [Nat.mod_mod_of_dvd' (by decide : 8 ∣ 32)])
@[simp] theorem UInt8.toUInt64_shiftRight (a b : UInt8) : (a >>> b).toUInt64 = a.toUInt64 >>> (b.toUInt64 % 8) :=
  UInt64.toBitVec_inj.1 (by simp [Nat.mod_mod_of_dvd' (by decide : 8 ∣ 64)])
@[simp] theorem UInt8.toUSize_shiftRight (a b : UInt8) : (a >>> b).toUSize = a.toUSize >>> (b.toUSize % 8) :=
  USize.toBitVec_inj.1 (by cases System.Platform.numBits_eq <;>
    simp_all [Nat.mod_mod_of_dvd' (by decide : 8 ∣ 32), Nat.mod_mod_of_dvd' (by decide : 8 ∣ 64)])

@[simp] theorem UInt16.toUInt32_shiftRight (a b : UInt16) : (a >>> b).toUInt32 = a.toUInt32 >>> (b.toUInt32 % 16) :=
  UInt32.toBitVec_inj.1 (by simp [Nat.mod_mod_of_dvd' (by decide : 16 ∣ 32)])
@[simp] theorem UInt16.toUInt64_shiftRight (a b : UInt16) : (a >>> b).toUInt64 = a.toUInt64 >>> (b.toUInt64 % 16) :=
  UInt64.toBitVec_inj.1 (by simp [Nat.mod_mod_of_dvd' (by decide : 16 ∣ 64)])
@[simp] theorem UInt16.toUSize_shiftRight (a b : UInt16) : (a >>> b).toUSize = a.toUSize >>> (b.toUSize % 16) :=
  USize.toBitVec_inj.1 (by cases System.Platform.numBits_eq <;>
    simp_all [Nat.mod_mod_of_dvd' (by decide : 16 ∣ 32), Nat.mod_mod_of_dvd' (by decide : 16 ∣ 64)])

@[simp] theorem UInt32.toUInt64_shiftRight (a b : UInt32) : (a >>> b).toUInt64 = a.toUInt64 >>> (b.toUInt64 % 32) :=
  UInt64.toBitVec_inj.1 (by simp [Nat.mod_mod_of_dvd' (by decide : 32 ∣ 64)])
@[simp] theorem UInt32.toUSize_shiftRight (a b : UInt32) : (a >>> b).toUSize = a.toUSize >>> (b.toUSize % 32) :=
  USize.toBitVec_inj.1 (by cases System.Platform.numBits_eq <;>
    simp_all [Nat.mod_mod_of_dvd' (by decide : 32 ∣ 32), Nat.mod_mod_of_dvd' (by decide : 32 ∣ 64)])

@[simp] theorem USize.toUInt64_shiftRight (a b : USize) : (a >>> b).toUInt64 = a.toUInt64 >>> (b.toUInt64 % UInt64.ofNat System.Platform.numBits) :=
  UInt64.toBitVec_inj.1 (by cases System.Platform.numBits_eq <;> simp_all [Nat.mod_mod_of_dvd' (by decide : 32 ∣ 64)])

/-!
There is no reasonable statement for`UInt16.toUInt8_shiftRight`; in fact for `a b : UInt16` the
expression `(a >>> b).toUInt8` is not a function of `a.toUInt8` and `b.toUInt8`.
-/

theorem BitVec.neg_one_mul (b : BitVec w) : -1#w * b = -b :=
  BitVec.eq_of_toInt_eq (by simp)

theorem BitVec.setWidth_add_eq_mod (x y : BitVec w) : BitVec.setWidth i (x + y) = (BitVec.setWidth i x + BitVec.setWidth i y) % (BitVec.twoPow i w) := by
  apply BitVec.eq_of_toNat_eq
  rw [toNat_setWidth]
  simp only [toNat_setWidth, toNat_add, toNat_umod, Nat.add_mod_mod, Nat.mod_add_mod, toNat_twoPow]
  by_cases h : i ≤ w
  · rw [Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 h), Nat.mod_zero, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 h)]
  · have hk : 2 ^ w < 2 ^ i := Nat.pow_lt_pow_of_lt (by decide) (Nat.lt_of_not_le h)
    rw [Nat.mod_eq_of_lt hk, Nat.mod_mod_eq_mod_mod_of_dvd (Nat.pow_dvd_pow _ (Nat.le_of_not_le h))]

theorem UInt8.sub_eq_add_mul (a b : UInt8) : a - b = a + 255 * b := by
  apply UInt8.toBitVec_inj.1
  simp only [UInt8.toBitVec_sub, BitVec.sub_toAdd, UInt8.toBitVec_add, UInt8.toBitVec_mul,
    toBitVec_ofNat, BitVec.add_right_inj]
  rw [← BitVec.neg_one_mul, BitVec.negOne_eq_allOnes]
  rfl

theorem UInt16.sub_eq_add_mul (a b : UInt16) : a - b = a + 65535 * b := by
  apply UInt16.toBitVec_inj.1
  simp only [UInt16.toBitVec_sub, BitVec.sub_toAdd, UInt16.toBitVec_add, UInt16.toBitVec_mul,
    toBitVec_ofNat, BitVec.add_right_inj]
  rw [← BitVec.neg_one_mul, BitVec.negOne_eq_allOnes]
  rfl

theorem UInt32.sub_eq_add_mul (a b : UInt32) : a - b = a + 4294967295 * b := by
  apply UInt32.toBitVec_inj.1
  simp only [UInt32.toBitVec_sub, BitVec.sub_toAdd, UInt32.toBitVec_add, UInt32.toBitVec_mul,
    toBitVec_ofNat, BitVec.add_right_inj]
  rw [← BitVec.neg_one_mul, BitVec.negOne_eq_allOnes]
  rfl

theorem UInt64.sub_eq_add_mul (a b : UInt64) : a - b = a + 18446744073709551615 * b := by
  apply UInt64.toBitVec_inj.1
  simp only [UInt64.toBitVec_sub, BitVec.sub_toAdd, UInt64.toBitVec_add, UInt64.toBitVec_mul,
    toBitVec_ofNat, BitVec.add_right_inj]
  rw [← BitVec.neg_one_mul, BitVec.negOne_eq_allOnes]
  rfl

theorem USize.sub_eq_add_mul (a b : USize) : a - b = a + USize.ofNatLT (USize.size - 1) (Nat.sub_one_lt (Nat.pos_iff_ne_zero.1 size_pos)) * b := by
  apply USize.toBitVec_inj.1
  simp only [USize.toBitVec_sub, BitVec.sub_toAdd, USize.toBitVec_add, USize.toBitVec_mul,
    toBitVec_ofNat, BitVec.add_right_inj]
  rw [← BitVec.neg_one_mul, BitVec.negOne_eq_allOnes]
  rfl

@[simp] theorem UInt8.ofNat_usizeSize_sub_one : UInt8.ofNat (USize.size - 1) = 255 := UInt8.toNat.inj (by simp)
@[simp] theorem UInt16.ofNat_usizeSize_sub_one : UInt16.ofNat (USize.size - 1) = 65535 := UInt16.toNat.inj (by simp)
@[simp] theorem UInt32.ofNat_usizeSize_sub_one : UInt32.ofNat (USize.size - 1) = 4294967295 := UInt32.toNat.inj (by simp)
@[simp] theorem USize.ofNat_uInt64Size_sub_one : USize.ofNat (UInt64.size - 1) = USize.ofNatLT (USize.size - 1) (Nat.sub_one_lt (Nat.pos_iff_ne_zero.1 size_pos)) :=
  USize.toNat.inj (by simp [USize.toNat_ofNat])

@[simp] theorem UInt16.toUInt8_sub (a b : UInt16) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  rw [UInt8.sub_eq_add_mul, UInt16.sub_eq_add_mul, toUInt8_add, toUInt8_mul, toUInt8_ofNat]; rfl

@[simp] theorem UInt32.toUInt8_sub (a b : UInt32) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  rw [UInt8.sub_eq_add_mul, UInt32.sub_eq_add_mul, toUInt8_add, toUInt8_mul, toUInt8_ofNat]; rfl
@[simp] theorem UInt32.toUInt16_sub (a b : UInt32) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := by
  rw [UInt16.sub_eq_add_mul, UInt32.sub_eq_add_mul, toUInt16_add, toUInt16_mul, toUInt16_ofNat]; rfl

@[simp] theorem UInt64.toUInt8_sub (a b : UInt64) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  rw [UInt8.sub_eq_add_mul, UInt64.sub_eq_add_mul, toUInt8_add, toUInt8_mul, toUInt8_ofNat]; rfl
@[simp] theorem UInt64.toUInt16_sub (a b : UInt64) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := by
  rw [UInt16.sub_eq_add_mul, UInt64.sub_eq_add_mul, toUInt16_add, toUInt16_mul, toUInt16_ofNat]; rfl
@[simp] theorem UInt64.toUInt32_sub (a b : UInt64) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := by
  rw [UInt32.sub_eq_add_mul, UInt64.sub_eq_add_mul, toUInt32_add, toUInt32_mul, toUInt32_ofNat]; rfl
@[simp] theorem UInt64.toUSize_sub (a b : UInt64) : (a - b).toUSize = a.toUSize - b.toUSize := by
  rw [USize.sub_eq_add_mul, UInt64.sub_eq_add_mul, toUSize_add, toUSize_mul, toUSize_ofNat,
    ← USize.ofNat_uInt64Size_sub_one]; rfl

@[simp] theorem USize.toUInt8_sub (a b : USize) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := by
  rw [UInt8.sub_eq_add_mul, USize.sub_eq_add_mul, toUInt8_add, toUInt8_mul, toUInt8_ofNatLT,
    UInt8.ofNat_usizeSize_sub_one]
@[simp] theorem USize.toUInt16_sub (a b : USize) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := by
  rw [UInt16.sub_eq_add_mul, USize.sub_eq_add_mul, toUInt16_add, toUInt16_mul, toUInt16_ofNatLT,
    UInt16.ofNat_usizeSize_sub_one]
@[simp] theorem USize.toUInt32_sub (a b : USize) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := by
  rw [UInt32.sub_eq_add_mul, USize.sub_eq_add_mul, toUInt32_add, toUInt32_mul, toUInt32_ofNatLT,
    UInt32.ofNat_usizeSize_sub_one]

@[simp] theorem UInt8.toUInt16_sub (a b : UInt8) : (a - b).toUInt16 = (a.toUInt16 - b.toUInt16) % 256 := by
  simp [UInt8.toUInt16_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt32_sub (a b : UInt8) : (a - b).toUInt32 = (a.toUInt32 - b.toUInt32) % 256 := by
  simp [UInt8.toUInt32_eq_mod_256_iff]
@[simp] theorem UInt8.toUInt64_sub (a b : UInt8) : (a - b).toUInt64 = (a.toUInt64 - b.toUInt64) % 256 := by
  simp [UInt8.toUInt64_eq_mod_256_iff]
@[simp] theorem UInt8.toUSize_sub (a b : UInt8) : (a - b).toUSize = (a.toUSize - b.toUSize) % 256 := by
  simp [UInt8.toUSize_eq_mod_256_iff]

@[simp] theorem UInt16.toUInt32_sub (a b : UInt16) : (a - b).toUInt32 = (a.toUInt32 - b.toUInt32) % 65536 := by
  simp [UInt16.toUInt32_eq_mod_65536_iff]
@[simp] theorem UInt16.toUInt64_sub (a b : UInt16) : (a - b).toUInt64 = (a.toUInt64 - b.toUInt64) % 65536 := by
  simp [UInt16.toUInt64_eq_mod_65536_iff]
@[simp] theorem UInt16.toUSize_sub (a b : UInt16) : (a - b).toUSize = (a.toUSize - b.toUSize) % 65536 := by
  simp [UInt16.toUSize_eq_mod_65536_iff]

@[simp] theorem UInt32.toUInt64_sub (a b : UInt32) : (a - b).toUInt64 = (a.toUInt64 - b.toUInt64) % 4294967296 := by
  simp [UInt32.toUInt64_eq_mod_4294967296_iff]
@[simp] theorem UInt32.toUSize_sub (a b : UInt32) : (a - b).toUSize = (a.toUSize - b.toUSize) % 4294967296 := by
  simp [UInt32.toUSize_eq_mod_4294967296_iff]

@[simp] theorem USize.toUInt64_sub (a b : USize) : (a - b).toUInt64 = (a.toUInt64 - b.toUInt64) % UInt64.ofNat USize.size := by
  simp [USize.toUInt64_eq_mod_usizeSize_iff]
