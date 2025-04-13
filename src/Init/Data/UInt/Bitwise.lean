/-
Copyright (c) 2024 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Mac Malone
-/
prelude
import Init.Data.UInt.Lemmas
import Init.Data.Fin.Bitwise

set_option hygiene false in
macro "declare_bitwise_uint_theorems" typeName:ident bits:term:arg : command =>
`(
namespace $typeName

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

@[simp] theorem UInt8.ofFin_and (a b : Fin UInt8.size) : UInt8.ofFin (a &&& b) = UInt8.ofFin a &&& UInt8.ofFin b := UInt8.toFin_inj.1 (by simp)
@[simp] theorem UInt16.ofFin_and (a b : Fin UInt16.size) : UInt16.ofFin (a &&& b) = UInt16.ofFin a &&& UInt16.ofFin b := UInt16.toFin_inj.1 (by simp)
@[simp] theorem UInt32.ofFin_and (a b : Fin UInt32.size) : UInt32.ofFin (a &&& b) = UInt32.ofFin a &&& UInt32.ofFin b := UInt32.toFin_inj.1 (by simp)
@[simp] theorem UInt64.ofFin_and (a b : Fin UInt64.size) : UInt64.ofFin (a &&& b) = UInt64.ofFin a &&& UInt64.ofFin b := UInt64.toFin_inj.1 (by simp)
@[simp] theorem USize.ofFin_and (a b : Fin USize.size) : USize.ofFin (a &&& b) = USize.ofFin a &&& USize.ofFin b := USize.toFin_inj.1 (by simp)

@[simp] theorem UInt8.ofBitVec_and (a b : BitVec 8) : UInt8.ofBitVec (a &&& b) = UInt8.ofBitVec a &&& UInt8.ofBitVec b := rfl
@[simp] theorem UInt16.ofBitVec_and (a b : BitVec 16) : UInt16.ofBitVec (a &&& b) = UInt16.ofBitVec a &&& UInt16.ofBitVec b := rfl
@[simp] theorem UInt32.ofBitVec_and (a b : BitVec 32) : UInt32.ofBitVec (a &&& b) = UInt32.ofBitVec a &&& UInt32.ofBitVec b := rfl
@[simp] theorem UInt64.ofBitVec_and (a b : BitVec 64) : UInt64.ofBitVec (a &&& b) = UInt64.ofBitVec a &&& UInt64.ofBitVec b := rfl
@[simp] theorem USize.ofBitVec_and (a b : BitVec System.Platform.numBits) : USize.ofBitVec (a &&& b) = USize.ofBitVec a &&& USize.ofBitVec b := rfl

@[simp] theorem UInt8.ofNat_and (a b : Nat) : UInt8.ofNat (a &&& b) = UInt8.ofNat a &&& UInt8.ofNat b :=
  UInt8.toBitVec_inj.1 (by simp [UInt8.toBitVec_ofNat'])
@[simp] theorem UInt16.ofNat_and (a b : Nat) : UInt16.ofNat (a &&& b) = UInt16.ofNat a &&& UInt16.ofNat b :=
  UInt16.toBitVec_inj.1 (by simp [UInt16.toBitVec_ofNat'])
@[simp] theorem UInt32.ofNat_and (a b : Nat) : UInt32.ofNat (a &&& b) = UInt32.ofNat a &&& UInt32.ofNat b :=
  UInt32.toBitVec_inj.1 (by simp [UInt32.toBitVec_ofNat'])
@[simp] theorem UInt64.ofNat_and (a b : Nat) : UInt64.ofNat (a &&& b) = UInt64.ofNat a &&& UInt64.ofNat b :=
  UInt64.toBitVec_inj.1 (by simp [UInt64.toBitVec_ofNat'])
@[simp] theorem USize.ofNat_and (a b : Nat) : USize.ofNat (a &&& b) = USize.ofNat a &&& USize.ofNat b :=
  USize.toBitVec_inj.1 (by simp [USize.toBitVec_ofNat'])

@[simp] theorem UInt8.ofNatLT_and (a b : Nat) (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    UInt8.ofNatLT (a &&& b) (Nat.and_lt_two_pow _ hb) = UInt8.ofNatLT a ha &&& UInt8.ofNatLT b hb := by
  simp [UInt8.ofNatLT_eq_ofNat]
@[simp] theorem UInt16.ofNatLT_and (a b : Nat) (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) :
    UInt16.ofNatLT (a &&& b) (Nat.and_lt_two_pow _ hb) = UInt16.ofNatLT a ha &&& UInt16.ofNatLT b hb := by
  simp [UInt16.ofNatLT_eq_ofNat]
@[simp] theorem UInt32.ofNatLT_and (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    UInt32.ofNatLT (a &&& b) (Nat.and_lt_two_pow _ hb) = UInt32.ofNatLT a ha &&& UInt32.ofNatLT b hb := by
  simp [UInt32.ofNatLT_eq_ofNat]
@[simp] theorem UInt64.ofNatLT_and (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNatLT (a &&& b) (Nat.and_lt_two_pow _ hb) = UInt64.ofNatLT a ha &&& UInt64.ofNatLT b hb := by
  simp [UInt64.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.ofFin_or (a b : Fin UInt8.size) : UInt8.ofFin (a ||| b) = UInt8.ofFin a ||| UInt8.ofFin b := UInt8.toFin_inj.1 (by simp)
@[simp] theorem UInt16.ofFin_or (a b : Fin UInt16.size) : UInt16.ofFin (a ||| b) = UInt16.ofFin a ||| UInt16.ofFin b := UInt16.toFin_inj.1 (by simp)
@[simp] theorem UInt32.ofFin_or (a b : Fin UInt32.size) : UInt32.ofFin (a ||| b) = UInt32.ofFin a ||| UInt32.ofFin b := UInt32.toFin_inj.1 (by simp)
@[simp] theorem UInt64.ofFin_or (a b : Fin UInt64.size) : UInt64.ofFin (a ||| b) = UInt64.ofFin a ||| UInt64.ofFin b := UInt64.toFin_inj.1 (by simp)
@[simp] theorem USize.ofFin_or (a b : Fin USize.size) : USize.ofFin (a ||| b) = USize.ofFin a ||| USize.ofFin b := USize.toFin_inj.1 (by simp)

@[simp] theorem UInt8.ofBitVec_or (a b : BitVec 8) : UInt8.ofBitVec (a ||| b) = UInt8.ofBitVec a ||| UInt8.ofBitVec b := rfl
@[simp] theorem UInt16.ofBitVec_or (a b : BitVec 16) : UInt16.ofBitVec (a ||| b) = UInt16.ofBitVec a ||| UInt16.ofBitVec b := rfl
@[simp] theorem UInt32.ofBitVec_or (a b : BitVec 32) : UInt32.ofBitVec (a ||| b) = UInt32.ofBitVec a ||| UInt32.ofBitVec b := rfl
@[simp] theorem UInt64.ofBitVec_or (a b : BitVec 64) : UInt64.ofBitVec (a ||| b) = UInt64.ofBitVec a ||| UInt64.ofBitVec b := rfl
@[simp] theorem USize.ofBitVec_or (a b : BitVec System.Platform.numBits) : USize.ofBitVec (a ||| b) = USize.ofBitVec a ||| USize.ofBitVec b := rfl

@[simp] theorem UInt8.ofNat_or (a b : Nat) : UInt8.ofNat (a ||| b) = UInt8.ofNat a ||| UInt8.ofNat b :=
  UInt8.toBitVec_inj.1 (by simp [UInt8.toBitVec_ofNat'])
@[simp] theorem UInt16.ofNat_or (a b : Nat) : UInt16.ofNat (a ||| b) = UInt16.ofNat a ||| UInt16.ofNat b :=
  UInt16.toBitVec_inj.1 (by simp [UInt16.toBitVec_ofNat'])
@[simp] theorem UInt32.ofNat_or (a b : Nat) : UInt32.ofNat (a ||| b) = UInt32.ofNat a ||| UInt32.ofNat b :=
  UInt32.toBitVec_inj.1 (by simp [UInt32.toBitVec_ofNat'])
@[simp] theorem UInt64.ofNat_or (a b : Nat) : UInt64.ofNat (a ||| b) = UInt64.ofNat a ||| UInt64.ofNat b :=
  UInt64.toBitVec_inj.1 (by simp [UInt64.toBitVec_ofNat'])
@[simp] theorem USize.ofNat_or (a b : Nat) : USize.ofNat (a ||| b) = USize.ofNat a ||| USize.ofNat b :=
  USize.toBitVec_inj.1 (by simp [USize.toBitVec_ofNat'])

@[simp] theorem UInt8.ofNatLT_or (a b : Nat) (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    UInt8.ofNatLT (a ||| b) (Nat.or_lt_two_pow ha hb) = UInt8.ofNatLT a ha ||| UInt8.ofNatLT b hb := by
  simp [UInt8.ofNatLT_eq_ofNat]
@[simp] theorem UInt16.ofNatLT_or (a b : Nat) (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) :
    UInt16.ofNatLT (a ||| b) (Nat.or_lt_two_pow ha hb) = UInt16.ofNatLT a ha ||| UInt16.ofNatLT b hb := by
  simp [UInt16.ofNatLT_eq_ofNat]
@[simp] theorem UInt32.ofNatLT_or (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    UInt32.ofNatLT (a ||| b) (Nat.or_lt_two_pow ha hb) = UInt32.ofNatLT a ha ||| UInt32.ofNatLT b hb := by
  simp [UInt32.ofNatLT_eq_ofNat]
@[simp] theorem UInt64.ofNatLT_or (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNatLT (a ||| b) (Nat.or_lt_two_pow ha hb) = UInt64.ofNatLT a ha ||| UInt64.ofNatLT b hb := by
  simp [UInt64.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.ofFin_xor (a b : Fin UInt8.size) : UInt8.ofFin (a ^^^ b) = UInt8.ofFin a ^^^ UInt8.ofFin b := UInt8.toFin_inj.1 (by simp)
@[simp] theorem UInt16.ofFin_xor (a b : Fin UInt16.size) : UInt16.ofFin (a ^^^ b) = UInt16.ofFin a ^^^ UInt16.ofFin b := UInt16.toFin_inj.1 (by simp)
@[simp] theorem UInt32.ofFin_xor (a b : Fin UInt32.size) : UInt32.ofFin (a ^^^ b) = UInt32.ofFin a ^^^ UInt32.ofFin b := UInt32.toFin_inj.1 (by simp)
@[simp] theorem UInt64.ofFin_xor (a b : Fin UInt64.size) : UInt64.ofFin (a ^^^ b) = UInt64.ofFin a ^^^ UInt64.ofFin b := UInt64.toFin_inj.1 (by simp)
@[simp] theorem USize.ofFin_xor (a b : Fin USize.size) : USize.ofFin (a ^^^ b) = USize.ofFin a ^^^ USize.ofFin b := USize.toFin_inj.1 (by simp)

@[simp] theorem UInt8.ofBitVec_xor (a b : BitVec 8) : UInt8.ofBitVec (a ^^^ b) = UInt8.ofBitVec a ^^^ UInt8.ofBitVec b := rfl
@[simp] theorem UInt16.ofBitVec_xor (a b : BitVec 16) : UInt16.ofBitVec (a ^^^ b) = UInt16.ofBitVec a ^^^ UInt16.ofBitVec b := rfl
@[simp] theorem UInt32.ofBitVec_xor (a b : BitVec 32) : UInt32.ofBitVec (a ^^^ b) = UInt32.ofBitVec a ^^^ UInt32.ofBitVec b := rfl
@[simp] theorem UInt64.ofBitVec_xor (a b : BitVec 64) : UInt64.ofBitVec (a ^^^ b) = UInt64.ofBitVec a ^^^ UInt64.ofBitVec b := rfl
@[simp] theorem USize.ofBitVec_xor (a b : BitVec System.Platform.numBits) : USize.ofBitVec (a ^^^ b) = USize.ofBitVec a ^^^ USize.ofBitVec b := rfl

@[simp] theorem UInt8.ofNat_xor (a b : Nat) : UInt8.ofNat (a ^^^ b) = UInt8.ofNat a ^^^ UInt8.ofNat b :=
  UInt8.toBitVec_inj.1 (by simp [UInt8.toBitVec_ofNat'])
@[simp] theorem UInt16.ofNat_xor (a b : Nat) : UInt16.ofNat (a ^^^ b) = UInt16.ofNat a ^^^ UInt16.ofNat b :=
  UInt16.toBitVec_inj.1 (by simp [UInt16.toBitVec_ofNat'])
@[simp] theorem UInt32.ofNat_xor (a b : Nat) : UInt32.ofNat (a ^^^ b) = UInt32.ofNat a ^^^ UInt32.ofNat b :=
  UInt32.toBitVec_inj.1 (by simp [UInt32.toBitVec_ofNat'])
@[simp] theorem UInt64.ofNat_xor (a b : Nat) : UInt64.ofNat (a ^^^ b) = UInt64.ofNat a ^^^ UInt64.ofNat b :=
  UInt64.toBitVec_inj.1 (by simp [UInt64.toBitVec_ofNat'])
@[simp] theorem USize.ofNat_xor (a b : Nat) : USize.ofNat (a ^^^ b) = USize.ofNat a ^^^ USize.ofNat b :=
  USize.toBitVec_inj.1 (by simp [USize.toBitVec_ofNat'])

@[simp] theorem UInt8.ofNatLT_xor (a b : Nat) (ha : a < 2 ^ 8) (hb : b < 2 ^ 8) :
    UInt8.ofNatLT (a ^^^ b) (Nat.xor_lt_two_pow ha hb) = UInt8.ofNatLT a ha ^^^ UInt8.ofNatLT b hb := by
  simp [UInt8.ofNatLT_eq_ofNat]
@[simp] theorem UInt16.ofNatLT_xor (a b : Nat) (ha : a < 2 ^ 16) (hb : b < 2 ^ 16) :
    UInt16.ofNatLT (a ^^^ b) (Nat.xor_lt_two_pow ha hb) = UInt16.ofNatLT a ha ^^^ UInt16.ofNatLT b hb := by
  simp [UInt16.ofNatLT_eq_ofNat]
@[simp] theorem UInt32.ofNatLT_xor (a b : Nat) (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) :
    UInt32.ofNatLT (a ^^^ b) (Nat.xor_lt_two_pow ha hb) = UInt32.ofNatLT a ha ^^^ UInt32.ofNatLT b hb := by
  simp [UInt32.ofNatLT_eq_ofNat]
@[simp] theorem UInt64.ofNatLT_xor (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    UInt64.ofNatLT (a ^^^ b) (Nat.xor_lt_two_pow ha hb) = UInt64.ofNatLT a ha ^^^ UInt64.ofNatLT b hb := by
  simp [UInt64.ofNatLT_eq_ofNat]

@[simp] theorem UInt8.ofBitVec_not (a : BitVec 8) : UInt8.ofBitVec (~~~a) = ~~~UInt8.ofBitVec a := rfl
@[simp] theorem UInt16.ofBitVec_not (a : BitVec 16) : UInt16.ofBitVec (~~~a) = ~~~UInt16.ofBitVec a := rfl
@[simp] theorem UInt32.ofBitVec_not (a : BitVec 32) : UInt32.ofBitVec (~~~a) = ~~~UInt32.ofBitVec a := rfl
@[simp] theorem UInt64.ofBitVec_not (a : BitVec 64) : UInt64.ofBitVec (~~~a) = ~~~UInt64.ofBitVec a := rfl
@[simp] theorem USize.ofBitVec_not (a : BitVec System.Platform.numBits) : USize.ofBitVec (~~~a) = ~~~USize.ofBitVec a := rfl

@[simp] theorem UInt8.ofFin_rev (a : Fin UInt8.size) : UInt8.ofFin a.rev = ~~~UInt8.ofFin a := UInt8.toFin_inj.1 (by simp)
@[simp] theorem UInt16.ofFin_rev (a : Fin UInt16.size) : UInt16.ofFin a.rev = ~~~UInt16.ofFin a := UInt16.toFin_inj.1 (by simp)
@[simp] theorem UInt32.ofFin_rev (a : Fin UInt32.size) : UInt32.ofFin a.rev = ~~~UInt32.ofFin a := UInt32.toFin_inj.1 (by simp)
@[simp] theorem UInt64.ofFin_rev (a : Fin UInt64.size) : UInt64.ofFin a.rev = ~~~UInt64.ofFin a := UInt64.toFin_inj.1 (by simp)
@[simp] theorem USize.ofFin_rev (a : Fin USize.size) : USize.ofFin a.rev = ~~~USize.ofFin a := USize.toFin_inj.1 (by simp)

@[simp] theorem UInt8.ofBitVec_shiftLeft (a : BitVec 8) (b : Nat) (hb : b < 8) : UInt8.ofBitVec (a <<< b) = UInt8.ofBitVec a <<< UInt8.ofNat b :=
  UInt8.toBitVec_inj.1 (by simp [Nat.mod_eq_of_lt hb])
@[simp] theorem UInt16.ofBitVec_shiftLeft (a : BitVec 16) (b : Nat) (hb : b < 16) : UInt16.ofBitVec (a <<< b) = UInt16.ofBitVec a <<< UInt16.ofNat b :=
  UInt16.toBitVec_inj.1 (by simp [Nat.mod_eq_of_lt hb])
@[simp] theorem UInt32.ofBitVec_shiftLeft (a : BitVec 32) (b : Nat) (hb : b < 32) : UInt32.ofBitVec (a <<< b) = UInt32.ofBitVec a <<< UInt32.ofNat b :=
  UInt32.toBitVec_inj.1 (by simp [Nat.mod_eq_of_lt hb])
@[simp] theorem UInt64.ofBitVec_shiftLeft (a : BitVec 64) (b : Nat) (hb : b < 64) : UInt64.ofBitVec (a <<< b) = UInt64.ofBitVec a <<< UInt64.ofNat b :=
  UInt64.toBitVec_inj.1 (by simp [Nat.mod_eq_of_lt hb])
@[simp] theorem USize.ofBitVec_shiftLeft (a : BitVec System.Platform.numBits) (b : Nat) (hb : b < System.Platform.numBits) :
    USize.ofBitVec (a <<< b) = USize.ofBitVec a <<< USize.ofNat b := by
  apply USize.toBitVec_inj.1
  simp only [USize.toBitVec_shiftLeft, BitVec.natCast_eq_ofNat, BitVec.shiftLeft_eq',
    BitVec.toNat_umod, toNat_toBitVec, toNat_ofNat', BitVec.toNat_ofNat, Nat.mod_two_pow_self]
  rw [Nat.mod_mod_of_dvd _ (by cases System.Platform.numBits_eq <;> simp_all), Nat.mod_eq_of_lt hb]

@[simp] theorem UInt8.ofBitVec_shiftLeft_mod (a : BitVec 8) (b : Nat) : UInt8.ofBitVec (a <<< (b % 8)) = UInt8.ofBitVec a <<< UInt8.ofNat b :=
  UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt16.ofBitVec_shiftLeft_mod (a : BitVec 16) (b : Nat) : UInt16.ofBitVec (a <<< (b % 16)) = UInt16.ofBitVec a <<< UInt16.ofNat b :=
  UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.ofBitVec_shiftLeft_mod (a : BitVec 32) (b : Nat) : UInt32.ofBitVec (a <<< (b % 32)) = UInt32.ofBitVec a <<< UInt32.ofNat b :=
  UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.ofBitVec_shiftLeft_mod (a : BitVec 64) (b : Nat) : UInt64.ofBitVec (a <<< (b % 64)) = UInt64.ofBitVec a <<< UInt64.ofNat b :=
  UInt64.toBitVec_inj.1 (by simp)
@[simp] theorem USize.ofBitVec_shiftLeft_mod (a : BitVec System.Platform.numBits) (b : Nat) :
    USize.ofBitVec (a <<< (b % System.Platform.numBits)) = USize.ofBitVec a <<< USize.ofNat b := by
  apply USize.toBitVec_inj.1
  simp only [USize.toBitVec_shiftLeft, BitVec.natCast_eq_ofNat, BitVec.shiftLeft_eq',
    BitVec.toNat_umod, toNat_toBitVec, toNat_ofNat', BitVec.toNat_ofNat, Nat.mod_two_pow_self]
  rw [Nat.mod_mod_of_dvd _ (by cases System.Platform.numBits_eq <;> simp_all)]

@[simp] theorem UInt8.ofFin_shiftLeft (a b : Fin UInt8.size) (hb : b < 8) : UInt8.ofFin (a <<< b) = UInt8.ofFin a <<< UInt8.ofFin b :=
  UInt8.toFin_inj.1 (by simp [UInt8.toFin_shiftLeft (ofFin a) (ofFin b) hb])
@[simp] theorem UInt16.ofFin_shiftLeft (a b : Fin UInt16.size) (hb : b < 16) : UInt16.ofFin (a <<< b) = UInt16.ofFin a <<< UInt16.ofFin b :=
  UInt16.toFin_inj.1 (by simp [UInt16.toFin_shiftLeft (ofFin a) (ofFin b) hb])
@[simp] theorem UInt32.ofFin_shiftLeft (a b : Fin UInt32.size) (hb : b < 32) : UInt32.ofFin (a <<< b) = UInt32.ofFin a <<< UInt32.ofFin b :=
  UInt32.toFin_inj.1 (by simp [UInt32.toFin_shiftLeft (ofFin a) (ofFin b) hb])
@[simp] theorem UInt64.ofFin_shiftLeft (a b : Fin UInt64.size) (hb : b < 64) : UInt64.ofFin (a <<< b) = UInt64.ofFin a <<< UInt64.ofFin b :=
  UInt64.toFin_inj.1 (by simp [UInt64.toFin_shiftLeft (ofFin a) (ofFin b) hb])
@[simp] theorem USize.ofFin_shiftLeft (a b : Fin USize.size) (hb : b < System.Platform.numBits) : USize.ofFin (a <<< b) = USize.ofFin a <<< USize.ofFin b :=
  USize.toFin_inj.1 (by simp [USize.toFin_shiftLeft (ofFin a) (ofFin b) hb])

@[simp] theorem UInt8.ofFin_shiftLeft_mod (a b : Fin UInt8.size) : UInt8.ofFin (a <<< (b % 8)) = UInt8.ofFin a <<< UInt8.ofFin b :=
  UInt8.toNat_inj.1 (by simp; rfl)
@[simp] theorem UInt16.ofFin_shiftLeft_mod (a b : Fin UInt16.size) : UInt16.ofFin (a <<< (b % 16)) = UInt16.ofFin a <<< UInt16.ofFin b :=
  UInt16.toNat_inj.1 (by simp; rfl)
@[simp] theorem UInt32.ofFin_shiftLeft_mod (a b : Fin UInt32.size) : UInt32.ofFin (a <<< (b % 32)) = UInt32.ofFin a <<< UInt32.ofFin b :=
  UInt32.toNat_inj.1 (by simp; rfl)
@[simp] theorem UInt64.ofFin_shiftLeft_mod (a b : Fin UInt64.size) : UInt64.ofFin (a <<< (b % 64)) = UInt64.ofFin a <<< UInt64.ofFin b :=
  UInt64.toNat_inj.1 (by simp; rfl)
@[simp] theorem USize.ofFin_shiftLeft_mod (a b : Fin USize.size) :
    USize.ofFin (a <<< (b % ⟨System.Platform.numBits, by cases System.Platform.numBits_eq <;> simp_all [USize.size]⟩)) = USize.ofFin a <<< USize.ofFin b := by
  apply USize.toFin_inj.1
  rw [toFin_ofFin, USize.shiftLeft_eq_shiftLeft_mod, USize.toFin_shiftLeft, toFin_ofFin, USize.toFin_mod,
    toFin_ofFin, toFin_ofNat', ← Fin.ofNat'_val_eq_self ⟨System.Platform.numBits, _⟩]
  rw [USize.toNat_mod, toNat_ofNat']
  cases System.Platform.numBits_eq <;> simpa [*] using Nat.mod_lt _ (by decide)

@[simp] theorem UInt8.ofNat_shiftLeft (a b : Nat) (hb : b < 8) :
    UInt8.ofNat (a <<< b) = UInt8.ofNat a <<< UInt8.ofNat b := by
  rw [UInt8.ofNat_eq_iff_mod_eq_toNat, UInt8.toNat_shiftLeft, toNat_ofNat', toNat_ofNat',
    Nat.mod_mod_of_dvd _ (by decide), Nat.mod_eq_of_lt hb, Nat.mod_two_pow_shiftLeft_mod_two_pow]
@[simp] theorem UInt16.ofNat_shiftLeft (a b : Nat) (hb : b < 16) :
    UInt16.ofNat (a <<< b) = UInt16.ofNat a <<< UInt16.ofNat b := by
  rw [UInt16.ofNat_eq_iff_mod_eq_toNat, UInt16.toNat_shiftLeft, toNat_ofNat', toNat_ofNat',
    Nat.mod_mod_of_dvd _ (by decide), Nat.mod_eq_of_lt hb, Nat.mod_two_pow_shiftLeft_mod_two_pow]
@[simp] theorem UInt32.ofNat_shiftLeft (a b : Nat) (hb : b < 32) :
    UInt32.ofNat (a <<< b) = UInt32.ofNat a <<< UInt32.ofNat b := by
  rw [UInt32.ofNat_eq_iff_mod_eq_toNat, UInt32.toNat_shiftLeft, toNat_ofNat', toNat_ofNat',
    Nat.mod_mod_of_dvd _ (by decide), Nat.mod_eq_of_lt hb, Nat.mod_two_pow_shiftLeft_mod_two_pow]
@[simp] theorem UInt64.ofNat_shiftLeft (a b : Nat) (hb : b < 64) :
    UInt64.ofNat (a <<< b) = UInt64.ofNat a <<< UInt64.ofNat b := by
  rw [UInt64.ofNat_eq_iff_mod_eq_toNat, UInt64.toNat_shiftLeft, toNat_ofNat', toNat_ofNat',
    Nat.mod_mod_of_dvd _ (by decide), Nat.mod_eq_of_lt hb, Nat.mod_two_pow_shiftLeft_mod_two_pow]
@[simp] theorem USize.ofNat_shiftLeft (a b : Nat) (hb : b < System.Platform.numBits) :
    USize.ofNat (a <<< b) = USize.ofNat a <<< USize.ofNat b := by
  rw [USize.ofNat_eq_iff_mod_eq_toNat, USize.toNat_shiftLeft, toNat_ofNat', toNat_ofNat',
    Nat.mod_mod_of_dvd _ _, Nat.mod_eq_of_lt hb, Nat.mod_two_pow_shiftLeft_mod_two_pow]
  cases System.Platform.numBits_eq <;> simp_all

@[simp] theorem UInt8.ofNatLT_shiftLeft {a b : Nat} (ha : a <<< b < UInt8.size) (hb : b < 8) :
    UInt8.ofNatLT (a <<< b) ha = UInt8.ofNatLT a (Nat.lt_of_shiftLeft_lt ha) <<< UInt8.ofNatLT b (Nat.lt_trans hb (by decide)) := by
  simp [UInt8.ofNatLT_eq_ofNat, UInt8.ofNat_shiftLeft a b hb]
@[simp] theorem UInt16.ofNatLT_shiftLeft {a b : Nat} (ha : a <<< b < UInt16.size) (hb : b < 16) :
    UInt16.ofNatLT (a <<< b) ha = UInt16.ofNatLT a (Nat.lt_of_shiftLeft_lt ha) <<< UInt16.ofNatLT b (Nat.lt_trans hb (by decide)) := by
  simp [UInt16.ofNatLT_eq_ofNat, UInt16.ofNat_shiftLeft a b hb]
@[simp] theorem UInt32.ofNatLT_shiftLeft {a b : Nat} (ha : a <<< b < UInt32.size) (hb : b < 32) :
    UInt32.ofNatLT (a <<< b) ha = UInt32.ofNatLT a (Nat.lt_of_shiftLeft_lt ha) <<< UInt32.ofNatLT b (Nat.lt_trans hb (by decide)) := by
  simp [UInt32.ofNatLT_eq_ofNat, UInt32.ofNat_shiftLeft a b hb]
@[simp] theorem UInt64.ofNatLT_shiftLeft {a b : Nat} (ha : a <<< b < UInt64.size) (hb : b < 64) :
    UInt64.ofNatLT (a <<< b) ha = UInt64.ofNatLT a (Nat.lt_of_shiftLeft_lt ha) <<< UInt64.ofNatLT b (Nat.lt_trans hb (by decide)) := by
  simp [UInt64.ofNatLT_eq_ofNat, UInt64.ofNat_shiftLeft a b hb]
@[simp] theorem USize.ofNatLT_shiftLeft {a b : Nat} (ha : a <<< b < USize.size) (hb : b < System.Platform.numBits) :
    USize.ofNatLT (a <<< b) ha = USize.ofNatLT a (Nat.lt_of_shiftLeft_lt ha) <<< USize.ofNatLT b (Nat.lt_trans hb Nat.lt_two_pow_self) := by
  simp [USize.ofNatLT_eq_ofNat, USize.ofNat_shiftLeft a b hb]

@[simp] theorem UInt8.ofBitVec_shiftRight (a : BitVec 8) (b : Nat) (hb : b < 8) : UInt8.ofBitVec (a >>> b) = UInt8.ofBitVec a >>> UInt8.ofNat b :=
  UInt8.toBitVec_inj.1 (by simp [Nat.mod_eq_of_lt hb])
@[simp] theorem UInt16.ofBitVec_shiftRight (a : BitVec 16) (b : Nat) (hb : b < 16) : UInt16.ofBitVec (a >>> b) = UInt16.ofBitVec a >>> UInt16.ofNat b :=
  UInt16.toBitVec_inj.1 (by simp [Nat.mod_eq_of_lt hb])
@[simp] theorem UInt32.ofBitVec_shiftRight (a : BitVec 32) (b : Nat) (hb : b < 32) : UInt32.ofBitVec (a >>> b) = UInt32.ofBitVec a >>> UInt32.ofNat b :=
  UInt32.toBitVec_inj.1 (by simp [Nat.mod_eq_of_lt hb])
@[simp] theorem UInt64.ofBitVec_shiftRight (a : BitVec 64) (b : Nat) (hb : b < 64) : UInt64.ofBitVec (a >>> b) = UInt64.ofBitVec a >>> UInt64.ofNat b :=
  UInt64.toBitVec_inj.1 (by simp [Nat.mod_eq_of_lt hb])
@[simp] theorem USize.ofBitVec_shiftRight (a : BitVec System.Platform.numBits) (b : Nat) (hb : b < System.Platform.numBits) :
    USize.ofBitVec (a >>> b) = USize.ofBitVec a >>> USize.ofNat b := by
  apply USize.toBitVec_inj.1
  simp only [USize.toBitVec_shiftRight, BitVec.natCast_eq_ofNat, BitVec.ushiftRight_eq',
    BitVec.toNat_umod, toNat_toBitVec, toNat_ofNat', BitVec.toNat_ofNat, Nat.mod_two_pow_self]
  rw [Nat.mod_mod_of_dvd _ (by cases System.Platform.numBits_eq <;> simp_all), Nat.mod_eq_of_lt hb]

@[simp] theorem UInt8.ofBitVec_shiftRight_mod (a : BitVec 8) (b : Nat) : UInt8.ofBitVec (a >>> (b % 8)) = UInt8.ofBitVec a >>> UInt8.ofNat b :=
  UInt8.toBitVec_inj.1 (by simp)
@[simp] theorem UInt16.ofBitVec_shiftRight_mod (a : BitVec 16) (b : Nat) : UInt16.ofBitVec (a >>> (b % 16)) = UInt16.ofBitVec a >>> UInt16.ofNat b :=
  UInt16.toBitVec_inj.1 (by simp)
@[simp] theorem UInt32.ofBitVec_shiftRight_mod (a : BitVec 32) (b : Nat) : UInt32.ofBitVec (a >>> (b % 32)) = UInt32.ofBitVec a >>> UInt32.ofNat b :=
  UInt32.toBitVec_inj.1 (by simp)
@[simp] theorem UInt64.ofBitVec_shiftRight_mod (a : BitVec 64) (b : Nat) : UInt64.ofBitVec (a >>> (b % 64)) = UInt64.ofBitVec a >>> UInt64.ofNat b :=
  UInt64.toBitVec_inj.1 (by simp)
@[simp] theorem USize.ofBitVec_shiftRight_mod (a : BitVec System.Platform.numBits) (b : Nat) :
    USize.ofBitVec (a >>> (b % System.Platform.numBits)) = USize.ofBitVec a >>> USize.ofNat b := by
  apply USize.toBitVec_inj.1
  simp only [USize.toBitVec_shiftRight, BitVec.natCast_eq_ofNat, BitVec.ushiftRight_eq',
    BitVec.toNat_umod, toNat_toBitVec, toNat_ofNat', BitVec.toNat_ofNat, Nat.mod_two_pow_self]
  rw [Nat.mod_mod_of_dvd _ (by cases System.Platform.numBits_eq <;> simp_all)]

@[simp] theorem UInt8.ofFin_shiftRight (a b : Fin UInt8.size) (hb : b < 8) : UInt8.ofFin (a >>> b) = UInt8.ofFin a >>> UInt8.ofFin b :=
  UInt8.toFin_inj.1 (by simp [UInt8.toFin_shiftRight (ofFin a) (ofFin b) hb])
@[simp] theorem UInt16.ofFin_shiftRight (a b : Fin UInt16.size) (hb : b < 16) : UInt16.ofFin (a >>> b) = UInt16.ofFin a >>> UInt16.ofFin b :=
  UInt16.toFin_inj.1 (by simp [UInt16.toFin_shiftRight (ofFin a) (ofFin b) hb])
@[simp] theorem UInt32.ofFin_shiftRight (a b : Fin UInt32.size) (hb : b < 32) : UInt32.ofFin (a >>> b) = UInt32.ofFin a >>> UInt32.ofFin b :=
  UInt32.toFin_inj.1 (by simp [UInt32.toFin_shiftRight (ofFin a) (ofFin b) hb])
@[simp] theorem UInt64.ofFin_shiftRight (a b : Fin UInt64.size) (hb : b < 64) : UInt64.ofFin (a >>> b) = UInt64.ofFin a >>> UInt64.ofFin b :=
  UInt64.toFin_inj.1 (by simp [UInt64.toFin_shiftRight (ofFin a) (ofFin b) hb])
@[simp] theorem USize.ofFin_shiftRight (a b : Fin USize.size) (hb : b < System.Platform.numBits) : USize.ofFin (a >>> b) = USize.ofFin a >>> USize.ofFin b :=
  USize.toFin_inj.1 (by simp [USize.toFin_shiftRight (ofFin a) (ofFin b) hb])

@[simp] theorem UInt8.ofFin_shiftRight_mod (a b : Fin UInt8.size) : UInt8.ofFin (a >>> (b % 8)) = UInt8.ofFin a >>> UInt8.ofFin b :=
  UInt8.toNat_inj.1 (by simp; rfl)
@[simp] theorem UInt16.ofFin_shiftRight_mod (a b : Fin UInt16.size) : UInt16.ofFin (a >>> (b % 16)) = UInt16.ofFin a >>> UInt16.ofFin b :=
  UInt16.toNat_inj.1 (by simp; rfl)
@[simp] theorem UInt32.ofFin_shiftRight_mod (a b : Fin UInt32.size) : UInt32.ofFin (a >>> (b % 32)) = UInt32.ofFin a >>> UInt32.ofFin b :=
  UInt32.toNat_inj.1 (by simp; rfl)
@[simp] theorem UInt64.ofFin_shiftRight_mod (a b : Fin UInt64.size) : UInt64.ofFin (a >>> (b % 64)) = UInt64.ofFin a >>> UInt64.ofFin b :=
  UInt64.toNat_inj.1 (by simp; rfl)
@[simp] theorem USize.ofFin_shiftRight_mod (a b : Fin USize.size) :
    USize.ofFin (a >>> (b % ⟨System.Platform.numBits, by cases System.Platform.numBits_eq <;> simp_all [USize.size]⟩)) = USize.ofFin a >>> USize.ofFin b := by
  apply USize.toFin_inj.1
  rw [toFin_ofFin, USize.shiftRight_eq_shiftRight_mod, USize.toFin_shiftRight, toFin_ofFin, USize.toFin_mod,
    toFin_ofFin, toFin_ofNat', ← Fin.ofNat'_val_eq_self ⟨System.Platform.numBits, _⟩]
  rw [USize.toNat_mod, toNat_ofNat']
  cases System.Platform.numBits_eq <;> simpa [*] using Nat.mod_lt _ (by decide)

theorem UInt8.neg_eq_not_add (a : UInt8) : -a = ~~~a + 1 := UInt8.toBitVec_inj.1 (BitVec.neg_eq_not_add _)
theorem UInt16.neg_eq_not_add (a : UInt16) : -a = ~~~a + 1 := UInt16.toBitVec_inj.1 (BitVec.neg_eq_not_add _)
theorem UInt32.neg_eq_not_add (a : UInt32) : -a = ~~~a + 1 := UInt32.toBitVec_inj.1 (BitVec.neg_eq_not_add _)
theorem UInt64.neg_eq_not_add (a : UInt64) : -a = ~~~a + 1 := UInt64.toBitVec_inj.1 (BitVec.neg_eq_not_add _)
theorem USize.neg_eq_not_add (a : USize) : -a = ~~~a + 1 := USize.toBitVec_inj.1 (BitVec.neg_eq_not_add _)

theorem UInt8.not_eq_neg_sub (a : UInt8) : ~~~a = -a - 1 := UInt8.toBitVec_inj.1 (BitVec.not_eq_neg_add _)
theorem UInt16.not_eq_neg_sub (a : UInt16) : ~~~a = -a - 1 := UInt16.toBitVec_inj.1 (BitVec.not_eq_neg_add _)
theorem UInt32.not_eq_neg_sub (a : UInt32) : ~~~a = -a - 1 := UInt32.toBitVec_inj.1 (BitVec.not_eq_neg_add _)
theorem UInt64.not_eq_neg_sub (a : UInt64) : ~~~a = -a - 1 := UInt64.toBitVec_inj.1 (BitVec.not_eq_neg_add _)
theorem USize.not_eq_neg_sub (a : USize) : ~~~a = -a - 1 := USize.toBitVec_inj.1 (BitVec.not_eq_neg_add _)

protected theorem UInt8.or_assoc (a b c : UInt8) : a ||| b ||| c = a ||| (b ||| c) := UInt8.toBitVec_inj.1 (BitVec.or_assoc _ _ _)
protected theorem UInt16.or_assoc (a b c : UInt16) : a ||| b ||| c = a ||| (b ||| c) := UInt16.toBitVec_inj.1 (BitVec.or_assoc _ _ _)
protected theorem UInt32.or_assoc (a b c : UInt32) : a ||| b ||| c = a ||| (b ||| c) := UInt32.toBitVec_inj.1 (BitVec.or_assoc _ _ _)
protected theorem UInt64.or_assoc (a b c : UInt64) : a ||| b ||| c = a ||| (b ||| c) := UInt64.toBitVec_inj.1 (BitVec.or_assoc _ _ _)
protected theorem USize.or_assoc (a b c : USize) : a ||| b ||| c = a ||| (b ||| c) := USize.toBitVec_inj.1 (BitVec.or_assoc _ _ _)

instance : Std.Associative (α := UInt8) (· ||| ·) := ⟨UInt8.or_assoc⟩
instance : Std.Associative (α := UInt16) (· ||| ·) := ⟨UInt16.or_assoc⟩
instance : Std.Associative (α := UInt32) (· ||| ·) := ⟨UInt32.or_assoc⟩
instance : Std.Associative (α := UInt64) (· ||| ·) := ⟨UInt64.or_assoc⟩
instance : Std.Associative (α := USize) (· ||| ·) := ⟨USize.or_assoc⟩

protected theorem UInt8.or_comm (a b : UInt8) : a ||| b = b ||| a := UInt8.toBitVec_inj.1 (BitVec.or_comm _ _)
protected theorem UInt16.or_comm (a b : UInt16) : a ||| b = b ||| a := UInt16.toBitVec_inj.1 (BitVec.or_comm _ _)
protected theorem UInt32.or_comm (a b : UInt32) : a ||| b = b ||| a := UInt32.toBitVec_inj.1 (BitVec.or_comm _ _)
protected theorem UInt64.or_comm (a b : UInt64) : a ||| b = b ||| a := UInt64.toBitVec_inj.1 (BitVec.or_comm _ _)
protected theorem USize.or_comm (a b : USize) : a ||| b = b ||| a := USize.toBitVec_inj.1 (BitVec.or_comm _ _)

instance : Std.Commutative (α := UInt8) (· ||| ·) := ⟨UInt8.or_comm⟩
instance : Std.Commutative (α := UInt16) (· ||| ·) := ⟨UInt16.or_comm⟩
instance : Std.Commutative (α := UInt32) (· ||| ·) := ⟨UInt32.or_comm⟩
instance : Std.Commutative (α := UInt64) (· ||| ·) := ⟨UInt64.or_comm⟩
instance : Std.Commutative (α := USize) (· ||| ·) := ⟨USize.or_comm⟩

@[simp] protected theorem UInt8.or_self {a : UInt8} : a ||| a = a := UInt8.toBitVec_inj.1 BitVec.or_self
@[simp] protected theorem UInt16.or_self {a : UInt16} : a ||| a = a := UInt16.toBitVec_inj.1 BitVec.or_self
@[simp] protected theorem UInt32.or_self {a : UInt32} : a ||| a = a := UInt32.toBitVec_inj.1 BitVec.or_self
@[simp] protected theorem UInt64.or_self {a : UInt64} : a ||| a = a := UInt64.toBitVec_inj.1 BitVec.or_self
@[simp] protected theorem USize.or_self {a : USize} : a ||| a = a := USize.toBitVec_inj.1 BitVec.or_self

instance : Std.IdempotentOp (α := UInt8) (· ||| ·) := ⟨fun _ => UInt8.or_self⟩
instance : Std.IdempotentOp (α := UInt16) (· ||| ·) := ⟨fun _ => UInt16.or_self⟩
instance : Std.IdempotentOp (α := UInt32) (· ||| ·) := ⟨fun _ => UInt32.or_self⟩
instance : Std.IdempotentOp (α := UInt64) (· ||| ·) := ⟨fun _ => UInt64.or_self⟩
instance : Std.IdempotentOp (α := USize) (· ||| ·) := ⟨fun _ => USize.or_self⟩

@[simp] protected theorem UInt8.or_zero {a : UInt8} : a ||| 0 = a := UInt8.toBitVec_inj.1 BitVec.or_zero
@[simp] protected theorem UInt16.or_zero {a : UInt16} : a ||| 0 = a := UInt16.toBitVec_inj.1 BitVec.or_zero
@[simp] protected theorem UInt32.or_zero {a : UInt32} : a ||| 0 = a := UInt32.toBitVec_inj.1 BitVec.or_zero
@[simp] protected theorem UInt64.or_zero {a : UInt64} : a ||| 0 = a := UInt64.toBitVec_inj.1 BitVec.or_zero
@[simp] protected theorem USize.or_zero {a : USize} : a ||| 0 = a := USize.toBitVec_inj.1 BitVec.or_zero

@[simp] protected theorem UInt8.zero_or {a : UInt8} : 0 ||| a = a := UInt8.toBitVec_inj.1 BitVec.zero_or
@[simp] protected theorem UInt16.zero_or {a : UInt16} : 0 ||| a = a := UInt16.toBitVec_inj.1 BitVec.zero_or
@[simp] protected theorem UInt32.zero_or {a : UInt32} : 0 ||| a = a := UInt32.toBitVec_inj.1 BitVec.zero_or
@[simp] protected theorem UInt64.zero_or {a : UInt64} : 0 ||| a = a := UInt64.toBitVec_inj.1 BitVec.zero_or
@[simp] protected theorem USize.zero_or {a : USize} : 0 ||| a = a := USize.toBitVec_inj.1 BitVec.zero_or

instance : Std.LawfulCommIdentity (α := UInt8) (· ||| ·) 0 where
  right_id _ := UInt8.or_zero
instance : Std.LawfulCommIdentity (α := UInt16) (· ||| ·) 0 where
  right_id _ := UInt16.or_zero
instance : Std.LawfulCommIdentity (α := UInt32) (· ||| ·) 0 where
  right_id _ := UInt32.or_zero
instance : Std.LawfulCommIdentity (α := UInt64) (· ||| ·) 0 where
  right_id _ := UInt64.or_zero
instance : Std.LawfulCommIdentity (α := USize) (· ||| ·) 0 where
  right_id _ := USize.or_zero

@[simp] theorem UInt8.neg_one_or {a : UInt8} : -1 ||| a = -1 := by
  rw [← UInt8.toBitVec_inj, UInt8.toBitVec_or, UInt8.toBitVec_neg, UInt8.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]
@[simp] theorem UInt16.neg_one_or {a : UInt16} : -1 ||| a = -1 := by
  rw [← UInt16.toBitVec_inj, UInt16.toBitVec_or, UInt16.toBitVec_neg, UInt16.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]
@[simp] theorem UInt32.neg_one_or {a : UInt32} : -1 ||| a = -1 := by
  rw [← UInt32.toBitVec_inj, UInt32.toBitVec_or, UInt32.toBitVec_neg, UInt32.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]
@[simp] theorem UInt64.neg_one_or {a : UInt64} : -1 ||| a = -1 := by
  rw [← UInt64.toBitVec_inj, UInt64.toBitVec_or, UInt64.toBitVec_neg, UInt64.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]
@[simp] theorem USize.neg_one_or {a : USize} : -1 ||| a = -1 := by
  rw [← USize.toBitVec_inj, USize.toBitVec_or, USize.toBitVec_neg, USize.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]

@[simp] theorem UInt8.or_neg_one {a : UInt8} : a ||| -1 = -1 := by rw [UInt8.or_comm, neg_one_or]
@[simp] theorem UInt16.or_neg_one {a : UInt16} : a ||| -1 = -1 := by rw [UInt16.or_comm, neg_one_or]
@[simp] theorem UInt32.or_neg_one {a : UInt32} : a ||| -1 = -1 := by rw [UInt32.or_comm, neg_one_or]
@[simp] theorem UInt64.or_neg_one {a : UInt64} : a ||| -1 = -1 := by rw [UInt64.or_comm, neg_one_or]
@[simp] theorem USize.or_neg_one {a : USize} : a ||| -1 = -1 := by rw [USize.or_comm, neg_one_or]

@[simp] theorem UInt8.or_eq_zero_iff {a b : UInt8} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.or_eq_zero_iff {a b : UInt16} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.or_eq_zero_iff {a b : UInt32} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.or_eq_zero_iff {a b : UInt64} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.or_eq_zero_iff {a b : USize} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← USize.toBitVec_inj]

protected theorem UInt8.and_assoc (a b c : UInt8) : a &&& b &&& c = a &&& (b &&& c) := UInt8.toBitVec_inj.1 (BitVec.and_assoc _ _ _)
protected theorem UInt16.and_assoc (a b c : UInt16) : a &&& b &&& c = a &&& (b &&& c) := UInt16.toBitVec_inj.1 (BitVec.and_assoc _ _ _)
protected theorem UInt32.and_assoc (a b c : UInt32) : a &&& b &&& c = a &&& (b &&& c) := UInt32.toBitVec_inj.1 (BitVec.and_assoc _ _ _)
protected theorem UInt64.and_assoc (a b c : UInt64) : a &&& b &&& c = a &&& (b &&& c) := UInt64.toBitVec_inj.1 (BitVec.and_assoc _ _ _)
protected theorem USize.and_assoc (a b c : USize) : a &&& b &&& c = a &&& (b &&& c) := USize.toBitVec_inj.1 (BitVec.and_assoc _ _ _)

instance : Std.Associative (α := UInt8) (· &&& ·) := ⟨UInt8.and_assoc⟩
instance : Std.Associative (α := UInt16) (· &&& ·) := ⟨UInt16.and_assoc⟩
instance : Std.Associative (α := UInt32) (· &&& ·) := ⟨UInt32.and_assoc⟩
instance : Std.Associative (α := UInt64) (· &&& ·) := ⟨UInt64.and_assoc⟩
instance : Std.Associative (α := USize) (· &&& ·) := ⟨USize.and_assoc⟩

protected theorem UInt8.and_comm (a b : UInt8) : a &&& b = b &&& a := UInt8.toBitVec_inj.1 (BitVec.and_comm _ _)
protected theorem UInt16.and_comm (a b : UInt16) : a &&& b = b &&& a := UInt16.toBitVec_inj.1 (BitVec.and_comm _ _)
protected theorem UInt32.and_comm (a b : UInt32) : a &&& b = b &&& a := UInt32.toBitVec_inj.1 (BitVec.and_comm _ _)
protected theorem UInt64.and_comm (a b : UInt64) : a &&& b = b &&& a := UInt64.toBitVec_inj.1 (BitVec.and_comm _ _)
protected theorem USize.and_comm (a b : USize) : a &&& b = b &&& a := USize.toBitVec_inj.1 (BitVec.and_comm _ _)

instance : Std.Commutative (α := UInt8) (· &&& ·) := ⟨UInt8.and_comm⟩
instance : Std.Commutative (α := UInt16) (· &&& ·) := ⟨UInt16.and_comm⟩
instance : Std.Commutative (α := UInt32) (· &&& ·) := ⟨UInt32.and_comm⟩
instance : Std.Commutative (α := UInt64) (· &&& ·) := ⟨UInt64.and_comm⟩
instance : Std.Commutative (α := USize) (· &&& ·) := ⟨USize.and_comm⟩

@[simp] protected theorem UInt8.and_self {a : UInt8} : a &&& a = a := UInt8.toBitVec_inj.1 BitVec.and_self
@[simp] protected theorem UInt16.and_self {a : UInt16} : a &&& a = a := UInt16.toBitVec_inj.1 BitVec.and_self
@[simp] protected theorem UInt32.and_self {a : UInt32} : a &&& a = a := UInt32.toBitVec_inj.1 BitVec.and_self
@[simp] protected theorem UInt64.and_self {a : UInt64} : a &&& a = a := UInt64.toBitVec_inj.1 BitVec.and_self
@[simp] protected theorem USize.and_self {a : USize} : a &&& a = a := USize.toBitVec_inj.1 BitVec.and_self

instance : Std.IdempotentOp (α := UInt8) (· &&& ·) := ⟨fun _ => UInt8.and_self⟩
instance : Std.IdempotentOp (α := UInt16) (· &&& ·) := ⟨fun _ => UInt16.and_self⟩
instance : Std.IdempotentOp (α := UInt32) (· &&& ·) := ⟨fun _ => UInt32.and_self⟩
instance : Std.IdempotentOp (α := UInt64) (· &&& ·) := ⟨fun _ => UInt64.and_self⟩
instance : Std.IdempotentOp (α := USize) (· &&& ·) := ⟨fun _ => USize.and_self⟩

@[simp] protected theorem UInt8.and_zero {a : UInt8} : a &&& 0 = 0 := UInt8.toBitVec_inj.1 BitVec.and_zero
@[simp] protected theorem UInt16.and_zero {a : UInt16} : a &&& 0 = 0 := UInt16.toBitVec_inj.1 BitVec.and_zero
@[simp] protected theorem UInt32.and_zero {a : UInt32} : a &&& 0 = 0 := UInt32.toBitVec_inj.1 BitVec.and_zero
@[simp] protected theorem UInt64.and_zero {a : UInt64} : a &&& 0 = 0 := UInt64.toBitVec_inj.1 BitVec.and_zero
@[simp] protected theorem USize.and_zero {a : USize} : a &&& 0 = 0 := USize.toBitVec_inj.1 BitVec.and_zero

@[simp] protected theorem UInt8.zero_and {a : UInt8} : 0 &&& a = 0 := UInt8.toBitVec_inj.1 BitVec.zero_and
@[simp] protected theorem UInt16.zero_and {a : UInt16} : 0 &&& a = 0 := UInt16.toBitVec_inj.1 BitVec.zero_and
@[simp] protected theorem UInt32.zero_and {a : UInt32} : 0 &&& a = 0 := UInt32.toBitVec_inj.1 BitVec.zero_and
@[simp] protected theorem UInt64.zero_and {a : UInt64} : 0 &&& a = 0 := UInt64.toBitVec_inj.1 BitVec.zero_and
@[simp] protected theorem USize.zero_and {a : USize} : 0 &&& a = 0 := USize.toBitVec_inj.1 BitVec.zero_and

@[simp] theorem UInt8.neg_one_and {a : UInt8} : -1 &&& a = a := by
  rw [← UInt8.toBitVec_inj, UInt8.toBitVec_and, UInt8.toBitVec_neg, UInt8.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]
@[simp] theorem UInt16.neg_one_and {a : UInt16} : -1 &&& a = a := by
  rw [← UInt16.toBitVec_inj, UInt16.toBitVec_and, UInt16.toBitVec_neg, UInt16.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]
@[simp] theorem UInt32.neg_one_and {a : UInt32} : -1 &&& a = a := by
  rw [← UInt32.toBitVec_inj, UInt32.toBitVec_and, UInt32.toBitVec_neg, UInt32.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]
@[simp] theorem UInt64.neg_one_and {a : UInt64} : -1 &&& a = a := by
  rw [← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_neg, UInt64.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]
@[simp] theorem USize.neg_one_and {a : USize} : -1 &&& a = a := by
  rw [← USize.toBitVec_inj, USize.toBitVec_and, USize.toBitVec_neg, USize.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]

@[simp] theorem UInt8.and_neg_one {a : UInt8} : a &&& -1 = a := by rw [UInt8.and_comm, neg_one_and]
@[simp] theorem UInt16.and_neg_one {a : UInt16} : a &&& -1 = a := by rw [UInt16.and_comm, neg_one_and]
@[simp] theorem UInt32.and_neg_one {a : UInt32} : a &&& -1 = a := by rw [UInt32.and_comm, neg_one_and]
@[simp] theorem UInt64.and_neg_one {a : UInt64} : a &&& -1 = a := by rw [UInt64.and_comm, neg_one_and]
@[simp] theorem USize.and_neg_one {a : USize} : a &&& -1 = a := by rw [USize.and_comm, neg_one_and]

instance : Std.LawfulCommIdentity (α := UInt8) (· &&& ·) (-1) where
  right_id _ := UInt8.and_neg_one
instance : Std.LawfulCommIdentity (α := UInt16) (· &&& ·) (-1) where
  right_id _ := UInt16.and_neg_one
instance : Std.LawfulCommIdentity (α := UInt32) (· &&& ·) (-1) where
  right_id _ := UInt32.and_neg_one
instance : Std.LawfulCommIdentity (α := UInt64) (· &&& ·) (-1) where
  right_id _ := UInt64.and_neg_one
instance : Std.LawfulCommIdentity (α := USize) (· &&& ·) (-1) where
  right_id _ := USize.and_neg_one

@[simp] theorem UInt8.and_eq_neg_one_iff {a b : UInt8} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← UInt8.toBitVec_inj, UInt8.toBitVec_and, UInt8.toBitVec_neg, UInt8.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]
@[simp] theorem UInt16.and_eq_neg_one_iff {a b : UInt16} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← UInt16.toBitVec_inj, UInt16.toBitVec_and, UInt16.toBitVec_neg, UInt16.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]
@[simp] theorem UInt32.and_eq_neg_one_iff {a b : UInt32} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← UInt32.toBitVec_inj, UInt32.toBitVec_and, UInt32.toBitVec_neg, UInt32.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]
@[simp] theorem UInt64.and_eq_neg_one_iff {a b : UInt64} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_neg, UInt64.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]
@[simp] theorem USize.and_eq_neg_one_iff {a b : USize} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← USize.toBitVec_inj, USize.toBitVec_and, USize.toBitVec_neg, USize.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]

protected theorem UInt8.xor_assoc (a b c : UInt8) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := UInt8.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)
protected theorem UInt16.xor_assoc (a b c : UInt16) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := UInt16.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)
protected theorem UInt32.xor_assoc (a b c : UInt32) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := UInt32.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)
protected theorem UInt64.xor_assoc (a b c : UInt64) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := UInt64.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)
protected theorem USize.xor_assoc (a b c : USize) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := USize.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)

instance : Std.Associative (α := UInt8) (· ^^^ ·) := ⟨UInt8.xor_assoc⟩
instance : Std.Associative (α := UInt16) (· ^^^ ·) := ⟨UInt16.xor_assoc⟩
instance : Std.Associative (α := UInt32) (· ^^^ ·) := ⟨UInt32.xor_assoc⟩
instance : Std.Associative (α := UInt64) (· ^^^ ·) := ⟨UInt64.xor_assoc⟩
instance : Std.Associative (α := USize) (· ^^^ ·) := ⟨USize.xor_assoc⟩

protected theorem UInt8.xor_comm (a b : UInt8) : a ^^^ b = b ^^^ a := UInt8.toBitVec_inj.1 (BitVec.xor_comm _ _)
protected theorem UInt16.xor_comm (a b : UInt16) : a ^^^ b = b ^^^ a := UInt16.toBitVec_inj.1 (BitVec.xor_comm _ _)
protected theorem UInt32.xor_comm (a b : UInt32) : a ^^^ b = b ^^^ a := UInt32.toBitVec_inj.1 (BitVec.xor_comm _ _)
protected theorem UInt64.xor_comm (a b : UInt64) : a ^^^ b = b ^^^ a := UInt64.toBitVec_inj.1 (BitVec.xor_comm _ _)
protected theorem USize.xor_comm (a b : USize) : a ^^^ b = b ^^^ a := USize.toBitVec_inj.1 (BitVec.xor_comm _ _)

instance : Std.Commutative (α := UInt8) (· ^^^ ·) := ⟨UInt8.xor_comm⟩
instance : Std.Commutative (α := UInt16) (· ^^^ ·) := ⟨UInt16.xor_comm⟩
instance : Std.Commutative (α := UInt32) (· ^^^ ·) := ⟨UInt32.xor_comm⟩
instance : Std.Commutative (α := UInt64) (· ^^^ ·) := ⟨UInt64.xor_comm⟩
instance : Std.Commutative (α := USize) (· ^^^ ·) := ⟨USize.xor_comm⟩

@[simp] protected theorem UInt8.xor_self {a : UInt8} : a ^^^ a = 0 := UInt8.toBitVec_inj.1 BitVec.xor_self
@[simp] protected theorem UInt16.xor_self {a : UInt16} : a ^^^ a = 0 := UInt16.toBitVec_inj.1 BitVec.xor_self
@[simp] protected theorem UInt32.xor_self {a : UInt32} : a ^^^ a = 0 := UInt32.toBitVec_inj.1 BitVec.xor_self
@[simp] protected theorem UInt64.xor_self {a : UInt64} : a ^^^ a = 0 := UInt64.toBitVec_inj.1 BitVec.xor_self
@[simp] protected theorem USize.xor_self {a : USize} : a ^^^ a = 0 := USize.toBitVec_inj.1 BitVec.xor_self

@[simp] protected theorem UInt8.xor_zero {a : UInt8} : a ^^^ 0 = a := UInt8.toBitVec_inj.1 BitVec.xor_zero
@[simp] protected theorem UInt16.xor_zero {a : UInt16} : a ^^^ 0 = a := UInt16.toBitVec_inj.1 BitVec.xor_zero
@[simp] protected theorem UInt32.xor_zero {a : UInt32} : a ^^^ 0 = a := UInt32.toBitVec_inj.1 BitVec.xor_zero
@[simp] protected theorem UInt64.xor_zero {a : UInt64} : a ^^^ 0 = a := UInt64.toBitVec_inj.1 BitVec.xor_zero
@[simp] protected theorem USize.xor_zero {a : USize} : a ^^^ 0 = a := USize.toBitVec_inj.1 BitVec.xor_zero

@[simp] protected theorem UInt8.zero_xor {a : UInt8} : 0 ^^^ a = a := UInt8.toBitVec_inj.1 BitVec.zero_xor
@[simp] protected theorem UInt16.zero_xor {a : UInt16} : 0 ^^^ a = a := UInt16.toBitVec_inj.1 BitVec.zero_xor
@[simp] protected theorem UInt32.zero_xor {a : UInt32} : 0 ^^^ a = a := UInt32.toBitVec_inj.1 BitVec.zero_xor
@[simp] protected theorem UInt64.zero_xor {a : UInt64} : 0 ^^^ a = a := UInt64.toBitVec_inj.1 BitVec.zero_xor
@[simp] protected theorem USize.zero_xor {a : USize} : 0 ^^^ a = a := USize.toBitVec_inj.1 BitVec.zero_xor

@[simp] theorem UInt8.neg_one_xor {a : UInt8} : -1 ^^^ a = ~~~a := by
  rw [← UInt8.toBitVec_inj, UInt8.toBitVec_xor, UInt8.toBitVec_neg, UInt8.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, UInt8.toBitVec_not]
@[simp] theorem UInt16.neg_one_xor {a : UInt16} : -1 ^^^ a = ~~~a := by
  rw [← UInt16.toBitVec_inj, UInt16.toBitVec_xor, UInt16.toBitVec_neg, UInt16.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, UInt16.toBitVec_not]
@[simp] theorem UInt32.neg_one_xor {a : UInt32} : -1 ^^^ a = ~~~a := by
  rw [← UInt32.toBitVec_inj, UInt32.toBitVec_xor, UInt32.toBitVec_neg, UInt32.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, UInt32.toBitVec_not]
@[simp] theorem UInt64.neg_one_xor {a : UInt64} : -1 ^^^ a = ~~~a := by
  rw [← UInt64.toBitVec_inj, UInt64.toBitVec_xor, UInt64.toBitVec_neg, UInt64.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, UInt64.toBitVec_not]
@[simp] theorem USize.neg_one_xor {a : USize} : -1 ^^^ a = ~~~a := by
  rw [← USize.toBitVec_inj, USize.toBitVec_xor, USize.toBitVec_neg, USize.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, USize.toBitVec_not]

@[simp] theorem UInt8.xor_neg_one {a : UInt8} : a ^^^ -1 = ~~~a := by rw [UInt8.xor_comm, neg_one_xor]
@[simp] theorem UInt16.xor_neg_one {a : UInt16} : a ^^^ -1 = ~~~a := by rw [UInt16.xor_comm, neg_one_xor]
@[simp] theorem UInt32.xor_neg_one {a : UInt32} : a ^^^ -1 = ~~~a := by rw [UInt32.xor_comm, neg_one_xor]
@[simp] theorem UInt64.xor_neg_one {a : UInt64} : a ^^^ -1 = ~~~a := by rw [UInt64.xor_comm, neg_one_xor]
@[simp] theorem USize.xor_neg_one {a : USize} : a ^^^ -1 = ~~~a := by rw [USize.xor_comm, neg_one_xor]

instance : Std.LawfulCommIdentity (α := UInt8) (· ^^^ ·) 0 where
  right_id _ := UInt8.xor_zero
instance : Std.LawfulCommIdentity (α := UInt16) (· ^^^ ·) 0  where
  right_id _ := UInt16.xor_zero
instance : Std.LawfulCommIdentity (α := UInt32) (· ^^^ ·) 0 where
  right_id _ := UInt32.xor_zero
instance : Std.LawfulCommIdentity (α := UInt64) (· ^^^ ·) 0 where
  right_id _ := UInt64.xor_zero
instance : Std.LawfulCommIdentity (α := USize) (· ^^^ ·) 0 where
  right_id _ := USize.xor_zero

@[simp] theorem UInt8.xor_eq_zero_iff {a b : UInt8} : a ^^^ b = 0 ↔ a = b := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.xor_eq_zero_iff {a b : UInt16} : a ^^^ b = 0 ↔ a = b := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.xor_eq_zero_iff {a b : UInt32} : a ^^^ b = 0 ↔ a = b := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.xor_eq_zero_iff {a b : UInt64} : a ^^^ b = 0 ↔ a = b := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.xor_eq_zero_iff {a b : USize} : a ^^^ b = 0 ↔ a = b := by simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.xor_left_inj {a b : UInt8} (c : UInt8) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.xor_left_inj {a b : UInt16} (c : UInt16) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.xor_left_inj {a b : UInt32} (c : UInt32) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.xor_left_inj {a b : UInt64} (c : UInt64) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.xor_left_inj {a b : USize} (c : USize) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.xor_right_inj {a b : UInt8} (c : UInt8) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.xor_right_inj {a b : UInt16} (c : UInt16) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.xor_right_inj {a b : UInt32} (c : UInt32) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.xor_right_inj {a b : UInt64} (c : UInt64) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.xor_right_inj {a b : USize} (c : USize) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.not_zero : ~~~(0 : UInt8) = -1 := rfl
@[simp] theorem UInt16.not_zero : ~~~(0 : UInt16) = -1 := rfl
@[simp] theorem UInt32.not_zero : ~~~(0 : UInt32) = -1 := rfl
@[simp] theorem UInt64.not_zero : ~~~(0 : UInt64) = -1 := rfl
@[simp] theorem USize.not_zero : ~~~(0 : USize) = -1 := by simp [USize.not_eq_neg_sub]

@[simp] theorem UInt8.not_neg_one : ~~~(-1 : UInt8) = 0 := rfl
@[simp] theorem UInt16.not_neg_one : ~~~(-1 : UInt16) = 0 := rfl
@[simp] theorem UInt32.not_neg_one : ~~~(-1 : UInt32) = 0 := rfl
@[simp] theorem UInt64.not_neg_one : ~~~(-1 : UInt64) = 0 := rfl
@[simp] theorem USize.not_neg_one : ~~~(-1 : USize) = 0 := by simp [USize.not_eq_neg_sub]

@[simp] theorem UInt8.not_not {a : UInt8} : ~~~(~~~a) = a := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.not_not {a : UInt16} : ~~~(~~~a) = a := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.not_not {a : UInt32} : ~~~(~~~a) = a := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.not_not {a : UInt64} : ~~~(~~~a) = a := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.not_not {a : USize} : ~~~(~~~a) = a := by simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.not_inj {a b : UInt8} : ~~~a = ~~~b ↔ a = b := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.not_inj {a b : UInt16} : ~~~a = ~~~b ↔ a = b := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.not_inj {a b : UInt32} : ~~~a = ~~~b ↔ a = b := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.not_inj {a b : UInt64} : ~~~a = ~~~b ↔ a = b := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.not_inj {a b : USize} : ~~~a = ~~~b ↔ a = b := by simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.and_not_self {a : UInt8} : a &&& ~~~a = 0 := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.and_not_self {a : UInt16} : a &&& ~~~a = 0 := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.and_not_self {a : UInt32} : a &&& ~~~a = 0 := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.and_not_self {a : UInt64} : a &&& ~~~a = 0 := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.and_not_self {a : USize} : a &&& ~~~a = 0 := by simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.not_and_self {a : UInt8} : ~~~a &&& a = 0 := by simp [UInt8.and_comm]
@[simp] theorem UInt16.not_and_self {a : UInt16} : ~~~a &&& a = 0 := by simp [UInt16.and_comm]
@[simp] theorem UInt32.not_and_self {a : UInt32} : ~~~a &&& a = 0 := by simp [UInt32.and_comm]
@[simp] theorem UInt64.not_and_self {a : UInt64} : ~~~a &&& a = 0 := by simp [UInt64.and_comm]
@[simp] theorem USize.not_and_self {a : USize} : ~~~a &&& a = 0 := by simp [USize.and_comm]

@[simp] theorem UInt8.or_not_self {a : UInt8} : a ||| ~~~a = -1 := by
  rw [← UInt8.toBitVec_inj, UInt8.toBitVec_or, UInt8.toBitVec_not, BitVec.or_not_self,
    UInt8.toBitVec_neg, UInt8.toBitVec_one, BitVec.neg_one_eq_allOnes]
@[simp] theorem UInt16.or_not_self {a : UInt16} : a ||| ~~~a = -1 := by
  rw [← UInt16.toBitVec_inj, UInt16.toBitVec_or, UInt16.toBitVec_not, BitVec.or_not_self,
    UInt16.toBitVec_neg, UInt16.toBitVec_one, BitVec.neg_one_eq_allOnes]
@[simp] theorem UInt32.or_not_self {a : UInt32} : a ||| ~~~a = -1 := by
  rw [← UInt32.toBitVec_inj, UInt32.toBitVec_or, UInt32.toBitVec_not, BitVec.or_not_self,
    UInt32.toBitVec_neg, UInt32.toBitVec_one, BitVec.neg_one_eq_allOnes]
@[simp] theorem UInt64.or_not_self {a : UInt64} : a ||| ~~~a = -1 := by
  rw [← UInt64.toBitVec_inj, UInt64.toBitVec_or, UInt64.toBitVec_not, BitVec.or_not_self,
    UInt64.toBitVec_neg, UInt64.toBitVec_one, BitVec.neg_one_eq_allOnes]
@[simp] theorem USize.or_not_self {a : USize} : a ||| ~~~a = -1 := by
  rw [← USize.toBitVec_inj, USize.toBitVec_or, USize.toBitVec_not, BitVec.or_not_self,
    USize.toBitVec_neg, USize.toBitVec_one, BitVec.neg_one_eq_allOnes]

@[simp] theorem UInt8.not_or_self {a : UInt8} : ~~~a ||| a = -1 := by simp [UInt8.or_comm]
@[simp] theorem UInt16.not_or_self {a : UInt16} : ~~~a ||| a = -1 := by simp [UInt16.or_comm]
@[simp] theorem UInt32.not_or_self {a : UInt32} : ~~~a ||| a = -1 := by simp [UInt32.or_comm]
@[simp] theorem UInt64.not_or_self {a : UInt64} : ~~~a ||| a = -1 := by simp [UInt64.or_comm]
@[simp] theorem USize.not_or_self {a : USize} : ~~~a ||| a = -1 := by simp [USize.or_comm]

theorem UInt8.not_eq_comm {a b : UInt8} : ~~~a = b ↔ a = ~~~b := by
  simp [← UInt8.toBitVec_inj, BitVec.not_eq_comm]
theorem UInt16.not_eq_comm {a b : UInt16} : ~~~a = b ↔ a = ~~~b := by
  simp [← UInt16.toBitVec_inj, BitVec.not_eq_comm]
theorem UInt32.not_eq_comm {a b : UInt32} : ~~~a = b ↔ a = ~~~b := by
  simp [← UInt32.toBitVec_inj, BitVec.not_eq_comm]
theorem UInt64.not_eq_comm {a b : UInt64} : ~~~a = b ↔ a = ~~~b := by
  simp [← UInt64.toBitVec_inj, BitVec.not_eq_comm]
theorem USize.not_eq_comm {a b : USize} : ~~~a = b ↔ a = ~~~b := by
  simp [← USize.toBitVec_inj, BitVec.not_eq_comm]

@[simp] theorem UInt8.ne_not_self {a : UInt8} : a ≠ ~~~a := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.ne_not_self {a : UInt16} : a ≠ ~~~a := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.ne_not_self {a : UInt32} : a ≠ ~~~a := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.ne_not_self {a : UInt64} : a ≠ ~~~a := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.ne_not_self {a : USize} : a ≠ ~~~a := by simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.not_ne_self {a : UInt8} : ~~~a ≠ a := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.not_ne_self {a : UInt16} : ~~~a ≠ a := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.not_ne_self {a : UInt32} : ~~~a ≠ a := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.not_ne_self {a : UInt64} : ~~~a ≠ a := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.not_ne_self {a : USize} : ~~~a ≠ a := by simp [← USize.toBitVec_inj]

theorem UInt8.not_xor {a b : UInt8} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← UInt8.toBitVec_inj, BitVec.not_xor_left]
theorem UInt16.not_xor {a b : UInt16} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← UInt16.toBitVec_inj, BitVec.not_xor_left]
theorem UInt32.not_xor {a b : UInt32} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← UInt32.toBitVec_inj, BitVec.not_xor_left]
theorem UInt64.not_xor {a b : UInt64} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← UInt64.toBitVec_inj, BitVec.not_xor_left]
theorem USize.not_xor {a b : USize} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← USize.toBitVec_inj, BitVec.not_xor_left]

theorem UInt8.xor_not {a b : UInt8} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← UInt8.toBitVec_inj, BitVec.not_xor_right]
theorem UInt16.xor_not {a b : UInt16} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← UInt16.toBitVec_inj, BitVec.not_xor_right]
theorem UInt32.xor_not {a b : UInt32} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← UInt32.toBitVec_inj, BitVec.not_xor_right]
theorem UInt64.xor_not {a b : UInt64} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← UInt64.toBitVec_inj, BitVec.not_xor_right]
theorem USize.xor_not {a b : USize} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← USize.toBitVec_inj, BitVec.not_xor_right]

@[simp] theorem UInt8.shiftLeft_zero {a : UInt8} : a <<< 0 = a := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.shiftLeft_zero {a : UInt16} : a <<< 0 = a := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.shiftLeft_zero {a : UInt32} : a <<< 0 = a := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.shiftLeft_zero {a : UInt64} : a <<< 0 = a := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.shiftLeft_zero {a : USize} : a <<< 0 = a := by simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.zero_shiftLeft {a : UInt8} : 0 <<< a = 0 := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.zero_shiftLeft {a : UInt16} : 0 <<< a = 0 := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.zero_shiftLeft {a : UInt32} : 0 <<< a = 0 := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.zero_shiftLeft {a : UInt64} : 0 <<< a = 0 := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.zero_shiftLeft {a : USize} : 0 <<< a = 0 := by simp [← USize.toBitVec_inj]

theorem UInt8.shiftLeft_xor {a b c : UInt8} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← UInt8.toBitVec_inj, BitVec.shiftLeft_xor_distrib]
theorem UInt16.shiftLeft_xor {a b c : UInt16} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← UInt16.toBitVec_inj, BitVec.shiftLeft_xor_distrib]
theorem UInt32.shiftLeft_xor {a b c : UInt32} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← UInt32.toBitVec_inj, BitVec.shiftLeft_xor_distrib]
theorem UInt64.shiftLeft_xor {a b c : UInt64} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← UInt64.toBitVec_inj, BitVec.shiftLeft_xor_distrib]
theorem USize.shiftLeft_xor {a b c : USize} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← USize.toBitVec_inj, BitVec.shiftLeft_xor_distrib]

theorem UInt8.shiftLeft_and {a b c : UInt8} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← UInt8.toBitVec_inj, BitVec.shiftLeft_and_distrib]
theorem UInt16.shiftLeft_and {a b c : UInt16} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← UInt16.toBitVec_inj, BitVec.shiftLeft_and_distrib]
theorem UInt32.shiftLeft_and {a b c : UInt32} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← UInt32.toBitVec_inj, BitVec.shiftLeft_and_distrib]
theorem UInt64.shiftLeft_and {a b c : UInt64} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← UInt64.toBitVec_inj, BitVec.shiftLeft_and_distrib]
theorem USize.shiftLeft_and {a b c : USize} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← USize.toBitVec_inj, BitVec.shiftLeft_and_distrib]

theorem UInt8.shiftLeft_or {a b c : UInt8} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← UInt8.toBitVec_inj, BitVec.shiftLeft_or_distrib]
theorem UInt16.shiftLeft_or {a b c : UInt16} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← UInt16.toBitVec_inj, BitVec.shiftLeft_or_distrib]
theorem UInt32.shiftLeft_or {a b c : UInt32} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← UInt32.toBitVec_inj, BitVec.shiftLeft_or_distrib]
theorem UInt64.shiftLeft_or {a b c : UInt64} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← UInt64.toBitVec_inj, BitVec.shiftLeft_or_distrib]
theorem USize.shiftLeft_or {a b c : USize} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← USize.toBitVec_inj, BitVec.shiftLeft_or_distrib]

theorem UInt8.shiftLeft_add_of_toNat_lt {a b c : UInt8} (h : b.toNat + c.toNat < 8) :
    a <<< (b + c) = (a <<< b) <<< c := by
  simp [← UInt8.toBitVec_inj, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show b.toNat < 8 by omega),
    Nat.mod_eq_of_lt (show c.toNat < 8 by omega), BitVec.shiftLeft_add]
theorem UInt16.shiftLeft_add_of_toNat_lt {a b c : UInt16} (h : b.toNat + c.toNat < 16) :
    a <<< (b + c) = (a <<< b) <<< c := by
  simp [← UInt16.toBitVec_inj, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show b.toNat < 16 by omega),
    Nat.mod_eq_of_lt (show c.toNat < 16 by omega), BitVec.shiftLeft_add]
theorem UInt32.shiftLeft_add_of_toNat_lt {a b c : UInt32} (h : b.toNat + c.toNat < 32) :
    a <<< (b + c) = (a <<< b) <<< c := by
  simp [← UInt32.toBitVec_inj, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show b.toNat < 32 by omega),
    Nat.mod_eq_of_lt (show c.toNat < 32 by omega), BitVec.shiftLeft_add]
theorem UInt64.shiftLeft_add_of_toNat_lt {a b c : UInt64} (h : b.toNat + c.toNat < 64) :
    a <<< (b + c) = (a <<< b) <<< c := by
  simp [← UInt64.toBitVec_inj, Nat.mod_eq_of_lt h, Nat.mod_eq_of_lt (show b.toNat < 64 by omega),
    Nat.mod_eq_of_lt (show c.toNat < 64 by omega), BitVec.shiftLeft_add]
theorem USize.shiftLeft_add_of_toNat_lt {a b c : USize}
    (h : b.toNat + c.toNat < System.Platform.numBits) :
    a <<< (b + c) = (a <<< b) <<< c := by
  simp only [← USize.toBitVec_inj, USize.toBitVec_shiftLeft, USize.toBitVec_add,
    BitVec.natCast_eq_ofNat, BitVec.shiftLeft_eq', BitVec.toNat_umod, BitVec.toNat_add,
    toNat_toBitVec, BitVec.toNat_ofNat, Nat.mod_two_pow_self]
  rw [Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, Nat.mod_eq_of_lt, BitVec.shiftLeft_add]
  · omega
  · omega
  · exact Nat.lt_trans h Nat.lt_two_pow_self
  · exact Nat.lt_of_le_of_lt (Nat.mod_le _ _) h

theorem UInt8.shiftLeft_add {a b c : UInt8} (hb : b < 8) (hc : c < 8) (hbc : b + c < 8) :
    a <<< (b + c) = (a <<< b) <<< c := by
  apply UInt8.shiftLeft_add_of_toNat_lt
  have hb : b.toNat < 8 := by simpa [lt_iff_toNat_lt] using hb
  have hc : c.toNat < 8 := by simpa [lt_iff_toNat_lt] using hc
  simp only [lt_iff_toNat_lt, UInt8.toNat_add, Nat.reducePow, UInt8.reduceToNat] at hbc
  rwa [Nat.mod_eq_of_lt (by omega)] at hbc
theorem UInt16.shiftLeft_add {a b c : UInt16} (hb : b < 16) (hc : c < 16) (hbc : b + c < 16) :
    a <<< (b + c) = (a <<< b) <<< c := by
  apply UInt16.shiftLeft_add_of_toNat_lt
  have hb : b.toNat < 16 := by simpa [lt_iff_toNat_lt] using hb
  have hc : c.toNat < 16 := by simpa [lt_iff_toNat_lt] using hc
  simp only [lt_iff_toNat_lt, UInt16.toNat_add, Nat.reducePow, UInt16.reduceToNat] at hbc
  rwa [Nat.mod_eq_of_lt (by omega)] at hbc
theorem UInt32.shiftLeft_add {a b c : UInt32} (hb : b < 32) (hc : c < 32) (hbc : b + c < 32) :
    a <<< (b + c) = (a <<< b) <<< c := by
  apply UInt32.shiftLeft_add_of_toNat_lt
  have hb : b.toNat < 32 := by simpa [lt_iff_toNat_lt] using hb
  have hc : c.toNat < 32 := by simpa [lt_iff_toNat_lt] using hc
  simp only [lt_iff_toNat_lt, UInt32.toNat_add, Nat.reducePow, UInt32.reduceToNat] at hbc
  rwa [Nat.mod_eq_of_lt (by omega)] at hbc
theorem UInt64.shiftLeft_add {a b c : UInt64} (hb : b < 64) (hc : c < 64) (hbc : b + c < 64) :
    a <<< (b + c) = (a <<< b) <<< c := by
  apply UInt64.shiftLeft_add_of_toNat_lt
  have hb : b.toNat < 64 := by simpa [lt_iff_toNat_lt] using hb
  have hc : c.toNat < 64 := by simpa [lt_iff_toNat_lt] using hc
  simp only [lt_iff_toNat_lt, UInt64.toNat_add, Nat.reducePow, UInt64.reduceToNat] at hbc
  rwa [Nat.mod_eq_of_lt (by omega)] at hbc
theorem USize.shiftLeft_add {a b c : USize} (hb : b < USize.ofNat System.Platform.numBits)
    (hc : c < USize.ofNat System.Platform.numBits) (hbc : b + c < USize.ofNat System.Platform.numBits) :
    a <<< (b + c) = (a <<< b) <<< c := by
  apply USize.shiftLeft_add_of_toNat_lt
  have hb : b.toNat < System.Platform.numBits := by simpa [lt_iff_toNat_lt] using hb
  have hc : c.toNat < System.Platform.numBits := by simpa [lt_iff_toNat_lt] using hc
  simp only [lt_iff_toNat_lt, USize.toNat_add, toNat_ofNat', Nat.mod_two_pow_self] at hbc
  rwa [Nat.mod_eq_of_lt] at hbc
  cases System.Platform.numBits_eq <;> simp_all <;> omega

@[simp] theorem UInt8.neg_one_shiftLeft_and_shiftLeft {a b : UInt8} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← UInt8.shiftLeft_and]
@[simp] theorem UInt16.neg_one_shiftLeft_and_shiftLeft {a b : UInt16} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← UInt16.shiftLeft_and]
@[simp] theorem UInt32.neg_one_shiftLeft_and_shiftLeft {a b : UInt32} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← UInt32.shiftLeft_and]
@[simp] theorem UInt64.neg_one_shiftLeft_and_shiftLeft {a b : UInt64} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← UInt64.shiftLeft_and]
@[simp] theorem USize.neg_one_shiftLeft_and_shiftLeft {a b : USize} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← USize.shiftLeft_and]

@[simp] theorem UInt8.neg_one_shiftLeft_or_shiftLeft {a b : UInt8} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← UInt8.shiftLeft_or]
@[simp] theorem UInt16.neg_one_shiftLeft_or_shiftLeft {a b : UInt16} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← UInt16.shiftLeft_or]
@[simp] theorem UInt32.neg_one_shiftLeft_or_shiftLeft {a b : UInt32} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← UInt32.shiftLeft_or]
@[simp] theorem UInt64.neg_one_shiftLeft_or_shiftLeft {a b : UInt8} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← UInt64.shiftLeft_or]
@[simp] theorem USize.neg_one_shiftLeft_or_shiftLeft {a b : USize} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← USize.shiftLeft_or]

@[simp] theorem UInt8.shiftRight_zero {a : UInt8} : a >>> 0 = a := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.shiftRight_zero {a : UInt16} : a >>> 0 = a := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.shiftRight_zero {a : UInt32} : a >>> 0 = a := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.shiftRight_zero {a : UInt64} : a >>> 0 = a := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.shiftRight_zero {a : USize} : a >>> 0 = a := by simp [← USize.toBitVec_inj]

@[simp] theorem UInt8.zero_shiftRight {a : UInt8} : 0 >>> a = 0 := by simp [← UInt8.toBitVec_inj]
@[simp] theorem UInt16.zero_shiftRight {a : UInt16} : 0 >>> a = 0 := by simp [← UInt16.toBitVec_inj]
@[simp] theorem UInt32.zero_shiftRight {a : UInt32} : 0 >>> a = 0 := by simp [← UInt32.toBitVec_inj]
@[simp] theorem UInt64.zero_shiftRight {a : UInt64} : 0 >>> a = 0 := by simp [← UInt64.toBitVec_inj]
@[simp] theorem USize.zero_shiftRight {a : USize} : 0 >>> a = 0 := by simp [← USize.toBitVec_inj]

theorem UInt8.shiftRight_xor {a b c : UInt8} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← UInt8.toBitVec_inj, BitVec.ushiftRight_xor_distrib]
theorem UInt16.shiftRight_xor {a b c : UInt16} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← UInt16.toBitVec_inj, BitVec.ushiftRight_xor_distrib]
theorem UInt32.shiftRight_xor {a b c : UInt32} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← UInt32.toBitVec_inj, BitVec.ushiftRight_xor_distrib]
theorem UInt64.shiftRight_xor {a b c : UInt64} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← UInt64.toBitVec_inj, BitVec.ushiftRight_xor_distrib]
theorem USize.shiftRight_xor {a b c : USize} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← USize.toBitVec_inj, BitVec.ushiftRight_xor_distrib]

theorem UInt8.shiftRight_and {a b c : UInt8} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← UInt8.toBitVec_inj, BitVec.ushiftRight_and_distrib]
theorem UInt16.shiftRight_and {a b c : UInt16} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← UInt16.toBitVec_inj, BitVec.ushiftRight_and_distrib]
theorem UInt32.shiftRight_and {a b c : UInt32} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← UInt32.toBitVec_inj, BitVec.ushiftRight_and_distrib]
theorem UInt64.shiftRight_and {a b c : UInt64} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← UInt64.toBitVec_inj, BitVec.ushiftRight_and_distrib]
theorem USize.shiftRight_and {a b c : USize} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← USize.toBitVec_inj, BitVec.ushiftRight_and_distrib]

theorem UInt8.shiftRight_or {a b c : UInt8} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← UInt8.toBitVec_inj, BitVec.ushiftRight_or_distrib]
theorem UInt16.shiftRight_or {a b c : UInt16} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← UInt16.toBitVec_inj, BitVec.ushiftRight_or_distrib]
theorem UInt32.shiftRight_or {a b c : UInt32} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← UInt32.toBitVec_inj, BitVec.ushiftRight_or_distrib]
theorem UInt64.shiftRight_or {a b c : UInt64} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← UInt64.toBitVec_inj, BitVec.ushiftRight_or_distrib]
theorem USize.shiftRight_or {a b c : USize} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← USize.toBitVec_inj, BitVec.ushiftRight_or_distrib]

theorem UInt8.and_le_right {a b : UInt8} : a &&& b ≤ b := by
  simpa [UInt8.le_iff_toNat_le] using Nat.and_le_right
theorem UInt16.and_le_right {a b : UInt16} : a &&& b ≤ b := by
  simpa [UInt16.le_iff_toNat_le] using Nat.and_le_right
theorem UInt32.and_le_right {a b : UInt32} : a &&& b ≤ b := by
  simpa [UInt32.le_iff_toNat_le] using Nat.and_le_right
theorem UInt64.and_le_right {a b : UInt64} : a &&& b ≤ b := by
  simpa [UInt64.le_iff_toNat_le] using Nat.and_le_right
theorem USize.and_le_right {a b : USize} : a &&& b ≤ b := by
  simpa [USize.le_iff_toNat_le] using Nat.and_le_right

theorem UInt8.and_le_left {a b : UInt8} : a &&& b ≤ a := by
  simpa [UInt8.le_iff_toNat_le] using Nat.and_le_left
theorem UInt16.and_le_left {a b : UInt16} : a &&& b ≤ a := by
  simpa [UInt16.le_iff_toNat_le] using Nat.and_le_left
theorem UInt32.and_le_left {a b : UInt32} : a &&& b ≤ a := by
  simpa [UInt32.le_iff_toNat_le] using Nat.and_le_left
theorem UInt64.and_le_left {a b : UInt64} : a &&& b ≤ a := by
  simpa [UInt64.le_iff_toNat_le] using Nat.and_le_left
theorem USize.and_le_left {a b : USize} : a &&& b ≤ a := by
  simpa [USize.le_iff_toNat_le] using Nat.and_le_left

theorem UInt8.left_le_or {a b : UInt8} : a ≤ a ||| b := by
  simpa [UInt8.le_iff_toNat_le] using Nat.left_le_or
theorem UInt16.left_le_or {a b : UInt16} : a ≤ a ||| b := by
  simpa [UInt16.le_iff_toNat_le] using Nat.left_le_or
theorem UInt32.left_le_or {a b : UInt32} : a ≤ a ||| b := by
  simpa [UInt32.le_iff_toNat_le] using Nat.left_le_or
theorem UInt64.left_le_or {a b : UInt64} : a ≤ a ||| b := by
  simpa [UInt64.le_iff_toNat_le] using Nat.left_le_or
theorem USize.left_le_or {a b : USize} : a ≤ a ||| b := by
  simpa [USize.le_iff_toNat_le] using Nat.left_le_or

theorem UInt8.right_le_or {a b : UInt8} : b ≤ a ||| b := by
  simpa [UInt8.le_iff_toNat_le] using Nat.right_le_or
theorem UInt16.right_le_or {a b : UInt16} : b ≤ a ||| b := by
  simpa [UInt16.le_iff_toNat_le] using Nat.right_le_or
theorem UInt32.right_le_or {a b : UInt32} : b ≤ a ||| b := by
  simpa [UInt32.le_iff_toNat_le] using Nat.right_le_or
theorem UInt64.right_le_or {a b : UInt64} : b ≤ a ||| b := by
  simpa [UInt64.le_iff_toNat_le] using Nat.right_le_or
theorem USize.right_le_or {a b : USize} : b ≤ a ||| b := by
  simpa [USize.le_iff_toNat_le] using Nat.right_le_or
