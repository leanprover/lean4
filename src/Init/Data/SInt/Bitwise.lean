/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.UInt.Bitwise
import Init.Data.SInt.Lemmas

set_option hygiene false in
macro "declare_bitwise_int_theorems" typeName:ident bits:term:arg : command =>
`(
namespace $typeName

@[simp, int_toBitVec] protected theorem toBitVec_not {a : $typeName} : (~~~a).toBitVec = ~~~a.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_and (a b : $typeName) : (a &&& b).toBitVec = a.toBitVec &&& b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_or (a b : $typeName) : (a ||| b).toBitVec = a.toBitVec ||| b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_xor (a b : $typeName) : (a ^^^ b).toBitVec = a.toBitVec ^^^ b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_shiftLeft (a b : $typeName) : (a <<< b).toBitVec = a.toBitVec <<< (b.toBitVec.smod $bits) := rfl
@[simp, int_toBitVec] protected theorem toBitVec_shiftRight (a b : $typeName) : (a >>> b).toBitVec = a.toBitVec.sshiftRight' (b.toBitVec.smod $bits) := rfl
@[simp, int_toBitVec] protected theorem toBitVec_abs (a : $typeName) : a.abs.toBitVec = a.toBitVec.abs := rfl

end $typeName
)
declare_bitwise_int_theorems Int8 8
declare_bitwise_int_theorems Int16 16
declare_bitwise_int_theorems Int32 32
declare_bitwise_int_theorems Int64 64
declare_bitwise_int_theorems ISize System.Platform.numBits

@[simp, int_toBitVec]
theorem Bool.toBitVec_toInt8 {b : Bool} : b.toInt8.toBitVec = (BitVec.ofBool b).setWidth 8 := by
  cases b <;> simp [toInt8]

@[simp, int_toBitVec]
theorem Bool.toBitVec_toInt16 {b : Bool} : b.toInt16.toBitVec = (BitVec.ofBool b).setWidth 16 := by
  cases b <;> simp [toInt16]

@[simp, int_toBitVec]
theorem Bool.toBitVec_toInt32 {b : Bool} : b.toInt32.toBitVec = (BitVec.ofBool b).setWidth 32 := by
  cases b <;> simp [toInt32]

@[simp, int_toBitVec]
theorem Bool.toBitVec_toInt64 {b : Bool} : b.toInt64.toBitVec = (BitVec.ofBool b).setWidth 64 := by
  cases b <;> simp [toInt64]

@[simp, int_toBitVec]
theorem Bool.toBitVec_toISize {b : Bool} :
    b.toISize.toBitVec = (BitVec.ofBool b).setWidth System.Platform.numBits := by
  cases b
  · simp [toISize]
  · apply BitVec.eq_of_toNat_eq
    simp [toISize]

@[simp] theorem UInt8.toInt8_and (a b : UInt8) : (a &&& b).toInt8 = a.toInt8 &&& b.toInt8 := rfl
@[simp] theorem UInt16.toInt16_and (a b : UInt16) : (a &&& b).toInt16 = a.toInt16 &&& b.toInt16 := rfl
@[simp] theorem UInt32.toInt32_and (a b : UInt32) : (a &&& b).toInt32 = a.toInt32 &&& b.toInt32 := rfl
@[simp] theorem UInt64.toInt64_and (a b : UInt64) : (a &&& b).toInt64 = a.toInt64 &&& b.toInt64 := rfl
@[simp] theorem USize.toISize_and (a b : USize) : (a &&& b).toISize = a.toISize &&& b.toISize := rfl

@[simp] theorem UInt8.toInt8_or (a b : UInt8) : (a ||| b).toInt8 = a.toInt8 ||| b.toInt8 := rfl
@[simp] theorem UInt16.toInt16_or (a b : UInt16) : (a ||| b).toInt16 = a.toInt16 ||| b.toInt16 := rfl
@[simp] theorem UInt32.toInt32_or (a b : UInt32) : (a ||| b).toInt32 = a.toInt32 ||| b.toInt32 := rfl
@[simp] theorem UInt64.toInt64_or (a b : UInt64) : (a ||| b).toInt64 = a.toInt64 ||| b.toInt64 := rfl
@[simp] theorem USize.toISize_or (a b : USize) : (a ||| b).toISize = a.toISize ||| b.toISize := rfl

@[simp] theorem UInt8.toInt8_xor (a b : UInt8) : (a ^^^ b).toInt8 = a.toInt8 ^^^ b.toInt8 := rfl
@[simp] theorem UInt16.toInt16_xor (a b : UInt16) : (a ^^^ b).toInt16 = a.toInt16 ^^^ b.toInt16 := rfl
@[simp] theorem UInt32.toInt32_xor (a b : UInt32) : (a ^^^ b).toInt32 = a.toInt32 ^^^ b.toInt32 := rfl
@[simp] theorem UInt64.toInt64_xor (a b : UInt64) : (a ^^^ b).toInt64 = a.toInt64 ^^^ b.toInt64 := rfl
@[simp] theorem USize.toISize_xor (a b : USize) : (a ^^^ b).toISize = a.toISize ^^^ b.toISize := rfl

@[simp] theorem UInt8.toInt8_not (a : UInt8) : (~~~a).toInt8 = ~~~a.toInt8 := rfl
@[simp] theorem UInt16.toInt16_not (a : UInt16) : (~~~a).toInt16 = ~~~a.toInt16 := rfl
@[simp] theorem UInt32.toInt32_not (a : UInt32) : (~~~a).toInt32 = ~~~a.toInt32 := rfl
@[simp] theorem UInt64.toInt64_not (a : UInt64) : (~~~a).toInt64 = ~~~a.toInt64 := rfl
@[simp] theorem USize.toISize_not (a : USize) : (~~~a).toISize = ~~~a.toISize := rfl

@[simp] theorem Int8.toUInt8_and (a b : Int8) : (a &&& b).toUInt8 = a.toUInt8 &&& b.toUInt8 := rfl
@[simp] theorem Int16.toUInt16_and (a b : Int16) : (a &&& b).toUInt16 = a.toUInt16 &&& b.toUInt16 := rfl
@[simp] theorem Int32.toUInt32_and (a b : Int32) : (a &&& b).toUInt32 = a.toUInt32 &&& b.toUInt32 := rfl
@[simp] theorem Int64.toUInt64_and (a b : Int64) : (a &&& b).toUInt64 = a.toUInt64 &&& b.toUInt64 := rfl
@[simp] theorem ISize.toUSize_and (a b : ISize) : (a &&& b).toUSize = a.toUSize &&& b.toUSize := rfl

@[simp] theorem Int8.toUInt8_or (a b : Int8) : (a ||| b).toUInt8 = a.toUInt8 ||| b.toUInt8 := rfl
@[simp] theorem Int16.toUInt16_or (a b : Int16) : (a ||| b).toUInt16 = a.toUInt16 ||| b.toUInt16 := rfl
@[simp] theorem Int32.toUInt32_or (a b : Int32) : (a ||| b).toUInt32 = a.toUInt32 ||| b.toUInt32 := rfl
@[simp] theorem Int64.toUInt64_or (a b : Int64) : (a ||| b).toUInt64 = a.toUInt64 ||| b.toUInt64 := rfl
@[simp] theorem ISize.toUSize_or (a b : ISize) : (a ||| b).toUSize = a.toUSize ||| b.toUSize := rfl

@[simp] theorem Int8.toUInt8_xor (a b : Int8) : (a ^^^ b).toUInt8 = a.toUInt8 ^^^ b.toUInt8 := rfl
@[simp] theorem Int16.toUInt16_xor (a b : Int16) : (a ^^^ b).toUInt16 = a.toUInt16 ^^^ b.toUInt16 := rfl
@[simp] theorem Int32.toUInt32_xor (a b : Int32) : (a ^^^ b).toUInt32 = a.toUInt32 ^^^ b.toUInt32 := rfl
@[simp] theorem Int64.toUInt64_xor (a b : Int64) : (a ^^^ b).toUInt64 = a.toUInt64 ^^^ b.toUInt64 := rfl
@[simp] theorem ISize.toUSize_xor (a b : ISize) : (a ^^^ b).toUSize = a.toUSize ^^^ b.toUSize := rfl

@[simp] theorem Int8.toUInt8_not (a : Int8) : (~~~a).toUInt8 = ~~~a.toUInt8 := rfl
@[simp] theorem Int16.toUInt16_not (a : Int16) : (~~~a).toUInt16 = ~~~a.toUInt16 := rfl
@[simp] theorem Int32.toUInt32_not (a : Int32) : (~~~a).toUInt32 = ~~~a.toUInt32 := rfl
@[simp] theorem Int64.toUInt64_not (a : Int64) : (~~~a).toUInt64 = ~~~a.toUInt64 := rfl
@[simp] theorem ISize.toUSize_not (a : ISize) : (~~~a).toUSize = ~~~a.toUSize := rfl

@[simp] theorem Int8.toInt16_and (a b : Int8) : (a &&& b).toInt16 = a.toInt16 &&& b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int8.toInt32_and (a b : Int8) : (a &&& b).toInt32 = a.toInt32 &&& b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem Int8.toInt64_and (a b : Int8) : (a &&& b).toInt64 = a.toInt64 &&& b.toInt64 := Int64.toBitVec_inj.1 (by simp)
@[simp] theorem Int8.toISize_and (a b : Int8) : (a &&& b).toISize = a.toISize &&& b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem Int16.toInt8_and (a b : Int16) : (a &&& b).toInt8 = a.toInt8 &&& b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int16.toInt32_and (a b : Int16) : (a &&& b).toInt32 = a.toInt32 &&& b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem Int16.toInt64_and (a b : Int16) : (a &&& b).toInt64 = a.toInt64 &&& b.toInt64 := Int64.toBitVec_inj.1 (by simp)
@[simp] theorem Int16.toISize_and (a b : Int16) : (a &&& b).toISize = a.toISize &&& b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem Int32.toInt8_and (a b : Int32) : (a &&& b).toInt8 = a.toInt8 &&& b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toInt16_and (a b : Int32) : (a &&& b).toInt16 = a.toInt16 &&& b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toInt64_and (a b : Int32) : (a &&& b).toInt64 = a.toInt64 &&& b.toInt64 := Int64.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toISize_and (a b : Int32) : (a &&& b).toISize = a.toISize &&& b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem ISize.toInt8_and (a b : ISize) : (a &&& b).toInt8 = a.toInt8 &&& b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt16_and (a b : ISize) : (a &&& b).toInt16 = a.toInt16 &&& b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt32_and (a b : ISize) : (a &&& b).toInt32 = a.toInt32 &&& b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt64_and (a b : ISize) : (a &&& b).toInt64 = a.toInt64 &&& b.toInt64 := Int64.toBitVec_inj.1 (by simp)

@[simp] theorem Int64.toInt8_and (a b : Int64) : (a &&& b).toInt8 = a.toInt8 &&& b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toInt16_and (a b : Int64) : (a &&& b).toInt16 = a.toInt16 &&& b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toInt32_and (a b : Int64) : (a &&& b).toInt32 = a.toInt32 &&& b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toISize_and (a b : Int64) : (a &&& b).toISize = a.toISize &&& b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem Int8.toInt16_or (a b : Int8) : (a ||| b).toInt16 = a.toInt16 ||| b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int8.toInt32_or (a b : Int8) : (a ||| b).toInt32 = a.toInt32 ||| b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem Int8.toInt64_or (a b : Int8) : (a ||| b).toInt64 = a.toInt64 ||| b.toInt64 := Int64.toBitVec_inj.1 (by simp)
@[simp] theorem Int8.toISize_or (a b : Int8) : (a ||| b).toISize = a.toISize ||| b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem Int16.toInt8_or (a b : Int16) : (a ||| b).toInt8 = a.toInt8 ||| b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int16.toInt32_or (a b : Int16) : (a ||| b).toInt32 = a.toInt32 ||| b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem Int16.toInt64_or (a b : Int16) : (a ||| b).toInt64 = a.toInt64 ||| b.toInt64 := Int64.toBitVec_inj.1 (by simp)
@[simp] theorem Int16.toISize_or (a b : Int16) : (a ||| b).toISize = a.toISize ||| b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem Int32.toInt8_or (a b : Int32) : (a ||| b).toInt8 = a.toInt8 ||| b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toInt16_or (a b : Int32) : (a ||| b).toInt16 = a.toInt16 ||| b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toInt64_or (a b : Int32) : (a ||| b).toInt64 = a.toInt64 ||| b.toInt64 := Int64.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toISize_or (a b : Int32) : (a ||| b).toISize = a.toISize ||| b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem ISize.toInt8_or (a b : ISize) : (a ||| b).toInt8 = a.toInt8 ||| b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt16_or (a b : ISize) : (a ||| b).toInt16 = a.toInt16 ||| b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt32_or (a b : ISize) : (a ||| b).toInt32 = a.toInt32 ||| b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt64_or (a b : ISize) : (a ||| b).toInt64 = a.toInt64 ||| b.toInt64 := Int64.toBitVec_inj.1 (by simp)

@[simp] theorem Int64.toInt8_or (a b : Int64) : (a ||| b).toInt8 = a.toInt8 ||| b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toInt16_or (a b : Int64) : (a ||| b).toInt16 = a.toInt16 ||| b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toInt32_or (a b : Int64) : (a ||| b).toInt32 = a.toInt32 ||| b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toISize_or (a b : Int64) : (a ||| b).toISize = a.toISize ||| b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem Int8.toInt16_xor (a b : Int8) : (a ^^^ b).toInt16 = a.toInt16 ^^^ b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int8.toInt32_xor (a b : Int8) : (a ^^^ b).toInt32 = a.toInt32 ^^^ b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem Int8.toInt64_xor (a b : Int8) : (a ^^^ b).toInt64 = a.toInt64 ^^^ b.toInt64 := Int64.toBitVec_inj.1 (by simp)
@[simp] theorem Int8.toISize_xor (a b : Int8) : (a ^^^ b).toISize = a.toISize ^^^ b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem Int16.toInt8_xor (a b : Int16) : (a ^^^ b).toInt8 = a.toInt8 ^^^ b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int16.toInt32_xor (a b : Int16) : (a ^^^ b).toInt32 = a.toInt32 ^^^ b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem Int16.toInt64_xor (a b : Int16) : (a ^^^ b).toInt64 = a.toInt64 ^^^ b.toInt64 := Int64.toBitVec_inj.1 (by simp)
@[simp] theorem Int16.toISize_xor (a b : Int16) : (a ^^^ b).toISize = a.toISize ^^^ b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem Int32.toInt8_xor (a b : Int32) : (a ^^^ b).toInt8 = a.toInt8 ^^^ b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toInt16_xor (a b : Int32) : (a ^^^ b).toInt16 = a.toInt16 ^^^ b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toInt64_xor (a b : Int32) : (a ^^^ b).toInt64 = a.toInt64 ^^^ b.toInt64 := Int64.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toISize_xor (a b : Int32) : (a ^^^ b).toISize = a.toISize ^^^ b.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem ISize.toInt8_xor (a b : ISize) : (a ^^^ b).toInt8 = a.toInt8 ^^^ b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt16_xor (a b : ISize) : (a ^^^ b).toInt16 = a.toInt16 ^^^ b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt32_xor (a b : ISize) : (a ^^^ b).toInt32 = a.toInt32 ^^^ b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt64_xor (a b : ISize) : (a ^^^ b).toInt64 = a.toInt64 ^^^ b.toInt64 := Int64.toBitVec_inj.1 (by simp)

@[simp] theorem Int64.toInt8_xor (a b : Int64) : (a ^^^ b).toInt8 = a.toInt8 ^^^ b.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toInt16_xor (a b : Int64) : (a ^^^ b).toInt16 = a.toInt16 ^^^ b.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toInt32_xor (a b : Int64) : (a ^^^ b).toInt32 = a.toInt32 ^^^ b.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toISize_xor (a b : Int64) : (a ^^^ b).toISize = a.toISize ^^^ b.toISize := ISize.toBitVec_inj.1 (by simp)

theorem Int8.not_eq_neg_add (a : Int8) : ~~~a = -a - 1 := Int8.toBitVec_inj.1 (by simpa using BitVec.not_eq_neg_add _)
theorem Int16.not_eq_neg_add (a : Int16) : ~~~a = -a - 1 := Int16.toBitVec_inj.1 (by simpa using BitVec.not_eq_neg_add _)
theorem Int32.not_eq_neg_add (a : Int32) : ~~~a = -a - 1 := Int32.toBitVec_inj.1 (by simpa using BitVec.not_eq_neg_add _)
theorem Int64.not_eq_neg_add (a : Int64) : ~~~a = -a - 1 := Int64.toBitVec_inj.1 (by simpa using BitVec.not_eq_neg_add _)
theorem ISize.not_eq_neg_add (a : ISize) : ~~~a = -a - 1 := ISize.toBitVec_inj.1 (by simpa using BitVec.not_eq_neg_add _)

@[simp] theorem Int8.toInt_not (a : Int8) : (~~~a).toInt = (-a.toInt - 1).bmod (2 ^ 8) := by simp [Int8.not_eq_neg_add]
@[simp] theorem Int16.toInt_not (a : Int16) : (~~~a).toInt = (-a.toInt - 1).bmod (2 ^ 16) := by simp [Int16.not_eq_neg_add]
@[simp] theorem Int32.toInt_not (a : Int32) : (~~~a).toInt = (-a.toInt - 1).bmod (2 ^ 32) := by simp [Int32.not_eq_neg_add]
@[simp] theorem Int64.toInt_not (a : Int64) : (~~~a).toInt = (-a.toInt - 1).bmod (2 ^ 64) := by simp [Int64.not_eq_neg_add]
@[simp] theorem ISize.toInt_not (a : ISize) : (~~~a).toInt = (-a.toInt - 1).bmod (2 ^ System.Platform.numBits) := by
  simp [ISize.not_eq_neg_add, toInt_neg]

@[simp] theorem Int16.toInt8_not (a : Int16) : (~~~a).toInt8 = ~~~a.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int32.toInt8_not (a : Int32) : (~~~a).toInt8 = ~~~a.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toInt8_not (a : Int64) : (~~~a).toInt8 = ~~~a.toInt8 := Int8.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt8_not (a : ISize) : (~~~a).toInt8 = ~~~a.toInt8 := Int8.toBitVec_inj.1 (by simp [System.Platform.numBits_pos])

@[simp] theorem Int32.toInt16_not (a : Int32) : (~~~a).toInt16 = ~~~a.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem Int64.toInt16_not (a : Int64) : (~~~a).toInt16 = ~~~a.toInt16 := Int16.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt16_not (a : ISize) : (~~~a).toInt16 = ~~~a.toInt16 := Int16.toBitVec_inj.1 (by simp [System.Platform.numBits_pos])

@[simp] theorem Int64.toInt32_not (a : Int64) : (~~~a).toInt32 = ~~~a.toInt32 := Int32.toBitVec_inj.1 (by simp)
@[simp] theorem ISize.toInt32_not (a : ISize) : (~~~a).toInt32 = ~~~a.toInt32 := Int32.toBitVec_inj.1 (by simp [System.Platform.numBits_pos])

@[simp] theorem Int64.toISize_not (a : Int64) : (~~~a).toISize = ~~~a.toISize := ISize.toBitVec_inj.1 (by simp)

@[simp] theorem Int8.ofBitVec_and (a b : BitVec 8) : Int8.ofBitVec (a &&& b) = Int8.ofBitVec a &&& Int8.ofBitVec b := rfl
@[simp] theorem Int16.ofBitVec_and (a b : BitVec 16) : Int16.ofBitVec (a &&& b) = Int16.ofBitVec a &&& Int16.ofBitVec b := rfl
@[simp] theorem Int32.ofBitVec_and (a b : BitVec 32) : Int32.ofBitVec (a &&& b) = Int32.ofBitVec a &&& Int32.ofBitVec b := rfl
@[simp] theorem Int64.ofBitVec_and (a b : BitVec 64) : Int64.ofBitVec (a &&& b) = Int64.ofBitVec a &&& Int64.ofBitVec b := rfl
@[simp] theorem ISize.ofBitVec_and (a b : BitVec System.Platform.numBits) : ISize.ofBitVec (a &&& b) = ISize.ofBitVec a &&& ISize.ofBitVec b := rfl

@[simp] theorem Int8.ofBitVec_or (a b : BitVec 8) : Int8.ofBitVec (a ||| b) = Int8.ofBitVec a ||| Int8.ofBitVec b := rfl
@[simp] theorem Int16.ofBitVec_or (a b : BitVec 16) : Int16.ofBitVec (a ||| b) = Int16.ofBitVec a ||| Int16.ofBitVec b := rfl
@[simp] theorem Int32.ofBitVec_or (a b : BitVec 32) : Int32.ofBitVec (a ||| b) = Int32.ofBitVec a ||| Int32.ofBitVec b := rfl
@[simp] theorem Int64.ofBitVec_or (a b : BitVec 64) : Int64.ofBitVec (a ||| b) = Int64.ofBitVec a ||| Int64.ofBitVec b := rfl
@[simp] theorem ISize.ofBitVec_or (a b : BitVec System.Platform.numBits) : ISize.ofBitVec (a ||| b) = ISize.ofBitVec a ||| ISize.ofBitVec b := rfl

@[simp] theorem Int8.ofBitVec_xor (a b : BitVec 8) : Int8.ofBitVec (a ^^^ b) = Int8.ofBitVec a ^^^ Int8.ofBitVec b := rfl
@[simp] theorem Int16.ofBitVec_xor (a b : BitVec 16) : Int16.ofBitVec (a ^^^ b) = Int16.ofBitVec a ^^^ Int16.ofBitVec b := rfl
@[simp] theorem Int32.ofBitVec_xor (a b : BitVec 32) : Int32.ofBitVec (a ^^^ b) = Int32.ofBitVec a ^^^ Int32.ofBitVec b := rfl
@[simp] theorem Int64.ofBitVec_xor (a b : BitVec 64) : Int64.ofBitVec (a ^^^ b) = Int64.ofBitVec a ^^^ Int64.ofBitVec b := rfl
@[simp] theorem ISize.ofBitVec_xor (a b : BitVec System.Platform.numBits) : ISize.ofBitVec (a ^^^ b) = ISize.ofBitVec a ^^^ ISize.ofBitVec b := rfl

@[simp] theorem Int8.ofBitVec_not (a : BitVec 8) : Int8.ofBitVec (~~~a) = ~~~Int8.ofBitVec a := rfl
@[simp] theorem Int16.ofBitVec_not (a : BitVec 16) : Int16.ofBitVec (~~~a) = ~~~Int16.ofBitVec a := rfl
@[simp] theorem Int32.ofBitVec_not (a : BitVec 32) : Int32.ofBitVec (~~~a) = ~~~Int32.ofBitVec a := rfl
@[simp] theorem Int64.ofBitVec_not (a : BitVec 64) : Int64.ofBitVec (~~~a) = ~~~Int64.ofBitVec a := rfl
@[simp] theorem ISize.ofBitVec_not (a : BitVec System.Platform.numBits) : ISize.ofBitVec (~~~a) = ~~~ISize.ofBitVec a := rfl

@[simp] theorem Int8.ofBitVec_intMin : Int8.ofBitVec (BitVec.intMin 8) = Int8.minValue := rfl
@[simp] theorem Int16.ofBitVec_intMin : Int16.ofBitVec (BitVec.intMin 16) = Int16.minValue := rfl
@[simp] theorem Int32.ofBitVec_intMin : Int32.ofBitVec (BitVec.intMin 32) = Int32.minValue := rfl
@[simp] theorem Int64.ofBitVec_intMin : Int64.ofBitVec (BitVec.intMin 64) = Int64.minValue := rfl
@[simp] theorem ISize.ofBitVec_intMin : ISize.ofBitVec (BitVec.intMin System.Platform.numBits) = ISize.minValue :=
  ISize.toBitVec_inj.1 (by simp [BitVec.intMin_eq_neg_two_pow])

@[simp] theorem Int8.ofBitVec_intMax : Int8.ofBitVec (BitVec.intMax 8) = Int8.maxValue := rfl
@[simp] theorem Int16.ofBitVec_intMax : Int16.ofBitVec (BitVec.intMax 16) = Int16.maxValue := rfl
@[simp] theorem Int32.ofBitVec_intMax : Int32.ofBitVec (BitVec.intMax 32) = Int32.maxValue := rfl
@[simp] theorem Int64.ofBitVec_intMax : Int64.ofBitVec (BitVec.intMax 64) = Int64.maxValue := rfl
@[simp] theorem ISize.ofBitVec_intMax : ISize.ofBitVec (BitVec.intMax System.Platform.numBits) = ISize.maxValue :=
  ISize.toInt_inj.1 (by rw [toInt_ofBitVec, BitVec.toInt_intMax, toInt_maxValue])

theorem Int8.neg_eq_not_add (a : Int8) : -a = ~~~a + 1 := Int8.toBitVec_inj.1 (BitVec.neg_eq_not_add _)
theorem Int16.neg_eq_not_add (a : Int16) : -a = ~~~a + 1 := Int16.toBitVec_inj.1 (BitVec.neg_eq_not_add _)
theorem Int32.neg_eq_not_add (a : Int32) : -a = ~~~a + 1 := Int32.toBitVec_inj.1 (BitVec.neg_eq_not_add _)
theorem Int64.neg_eq_not_add (a : Int64) : -a = ~~~a + 1 := Int64.toBitVec_inj.1 (BitVec.neg_eq_not_add _)
theorem ISize.neg_eq_not_add (a : ISize) : -a = ~~~a + 1 := ISize.toBitVec_inj.1 (BitVec.neg_eq_not_add _)

theorem Int8.not_eq_neg_sub (a : Int8) : ~~~a = -a - 1 := Int8.toBitVec_inj.1 (BitVec.not_eq_neg_add _)
theorem Int16.not_eq_neg_sub (a : Int16) : ~~~a = -a - 1 := Int16.toBitVec_inj.1 (BitVec.not_eq_neg_add _)
theorem Int32.not_eq_neg_sub (a : Int32) : ~~~a = -a - 1 := Int32.toBitVec_inj.1 (BitVec.not_eq_neg_add _)
theorem Int64.not_eq_neg_sub (a : Int64) : ~~~a = -a - 1 := Int64.toBitVec_inj.1 (BitVec.not_eq_neg_add _)
theorem ISize.not_eq_neg_sub (a : ISize) : ~~~a = -a - 1 := ISize.toBitVec_inj.1 (BitVec.not_eq_neg_add _)

protected theorem Int8.or_assoc (a b c : Int8) : a ||| b ||| c = a ||| (b ||| c) := Int8.toBitVec_inj.1 (BitVec.or_assoc _ _ _)
protected theorem Int16.or_assoc (a b c : Int16) : a ||| b ||| c = a ||| (b ||| c) := Int16.toBitVec_inj.1 (BitVec.or_assoc _ _ _)
protected theorem Int32.or_assoc (a b c : Int32) : a ||| b ||| c = a ||| (b ||| c) := Int32.toBitVec_inj.1 (BitVec.or_assoc _ _ _)
protected theorem Int64.or_assoc (a b c : Int64) : a ||| b ||| c = a ||| (b ||| c) := Int64.toBitVec_inj.1 (BitVec.or_assoc _ _ _)
protected theorem ISize.or_assoc (a b c : ISize) : a ||| b ||| c = a ||| (b ||| c) := ISize.toBitVec_inj.1 (BitVec.or_assoc _ _ _)

instance : Std.Associative (α := Int8) (· ||| ·) := ⟨Int8.or_assoc⟩
instance : Std.Associative (α := Int16) (· ||| ·) := ⟨Int16.or_assoc⟩
instance : Std.Associative (α := Int32) (· ||| ·) := ⟨Int32.or_assoc⟩
instance : Std.Associative (α := Int64) (· ||| ·) := ⟨Int64.or_assoc⟩
instance : Std.Associative (α := ISize) (· ||| ·) := ⟨ISize.or_assoc⟩

protected theorem Int8.or_comm (a b : Int8) : a ||| b = b ||| a := Int8.toBitVec_inj.1 (BitVec.or_comm _ _)
protected theorem Int16.or_comm (a b : Int16) : a ||| b = b ||| a := Int16.toBitVec_inj.1 (BitVec.or_comm _ _)
protected theorem Int32.or_comm (a b : Int32) : a ||| b = b ||| a := Int32.toBitVec_inj.1 (BitVec.or_comm _ _)
protected theorem Int64.or_comm (a b : Int64) : a ||| b = b ||| a := Int64.toBitVec_inj.1 (BitVec.or_comm _ _)
protected theorem ISize.or_comm (a b : ISize) : a ||| b = b ||| a := ISize.toBitVec_inj.1 (BitVec.or_comm _ _)

instance : Std.Commutative (α := Int8) (· ||| ·) := ⟨Int8.or_comm⟩
instance : Std.Commutative (α := Int16) (· ||| ·) := ⟨Int16.or_comm⟩
instance : Std.Commutative (α := Int32) (· ||| ·) := ⟨Int32.or_comm⟩
instance : Std.Commutative (α := Int64) (· ||| ·) := ⟨Int64.or_comm⟩
instance : Std.Commutative (α := ISize) (· ||| ·) := ⟨ISize.or_comm⟩

@[simp] protected theorem Int8.or_self {a : Int8} : a ||| a = a := Int8.toBitVec_inj.1 BitVec.or_self
@[simp] protected theorem Int16.or_self {a : Int16} : a ||| a = a := Int16.toBitVec_inj.1 BitVec.or_self
@[simp] protected theorem Int32.or_self {a : Int32} : a ||| a = a := Int32.toBitVec_inj.1 BitVec.or_self
@[simp] protected theorem Int64.or_self {a : Int64} : a ||| a = a := Int64.toBitVec_inj.1 BitVec.or_self
@[simp] protected theorem ISize.or_self {a : ISize} : a ||| a = a := ISize.toBitVec_inj.1 BitVec.or_self

instance : Std.IdempotentOp (α := Int8) (· ||| ·) := ⟨fun _ => Int8.or_self⟩
instance : Std.IdempotentOp (α := Int16) (· ||| ·) := ⟨fun _ => Int16.or_self⟩
instance : Std.IdempotentOp (α := Int32) (· ||| ·) := ⟨fun _ => Int32.or_self⟩
instance : Std.IdempotentOp (α := Int64) (· ||| ·) := ⟨fun _ => Int64.or_self⟩
instance : Std.IdempotentOp (α := ISize) (· ||| ·) := ⟨fun _ => ISize.or_self⟩

@[simp] protected theorem Int8.or_zero {a : Int8} : a ||| 0 = a := Int8.toBitVec_inj.1 BitVec.or_zero
@[simp] protected theorem Int16.or_zero {a : Int16} : a ||| 0 = a := Int16.toBitVec_inj.1 BitVec.or_zero
@[simp] protected theorem Int32.or_zero {a : Int32} : a ||| 0 = a := Int32.toBitVec_inj.1 BitVec.or_zero
@[simp] protected theorem Int64.or_zero {a : Int64} : a ||| 0 = a := Int64.toBitVec_inj.1 BitVec.or_zero
@[simp] protected theorem ISize.or_zero {a : ISize} : a ||| 0 = a := ISize.toBitVec_inj.1 BitVec.or_zero

@[simp] protected theorem Int8.zero_or {a : Int8} : 0 ||| a = a := Int8.toBitVec_inj.1 BitVec.zero_or
@[simp] protected theorem Int16.zero_or {a : Int16} : 0 ||| a = a := Int16.toBitVec_inj.1 BitVec.zero_or
@[simp] protected theorem Int32.zero_or {a : Int32} : 0 ||| a = a := Int32.toBitVec_inj.1 BitVec.zero_or
@[simp] protected theorem Int64.zero_or {a : Int64} : 0 ||| a = a := Int64.toBitVec_inj.1 BitVec.zero_or
@[simp] protected theorem ISize.zero_or {a : ISize} : 0 ||| a = a := ISize.toBitVec_inj.1 BitVec.zero_or

instance : Std.LawfulCommIdentity (α := Int8) (· ||| ·) 0 where
  right_id _ := Int8.or_zero
instance : Std.LawfulCommIdentity (α := Int16) (· ||| ·) 0 where
  right_id _ := Int16.or_zero
instance : Std.LawfulCommIdentity (α := Int32) (· ||| ·) 0 where
  right_id _ := Int32.or_zero
instance : Std.LawfulCommIdentity (α := Int64) (· ||| ·) 0 where
  right_id _ := Int64.or_zero
instance : Std.LawfulCommIdentity (α := ISize) (· ||| ·) 0 where
  right_id _ := ISize.or_zero

@[simp] theorem Int8.neg_one_or {a : Int8} : -1 ||| a = -1 := by
  rw [← Int8.toBitVec_inj, Int8.toBitVec_or, Int8.toBitVec_neg, Int8.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]
@[simp] theorem Int16.neg_one_or {a : Int16} : -1 ||| a = -1 := by
  rw [← Int16.toBitVec_inj, Int16.toBitVec_or, Int16.toBitVec_neg, Int16.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]
@[simp] theorem Int32.neg_one_or {a : Int32} : -1 ||| a = -1 := by
  rw [← Int32.toBitVec_inj, Int32.toBitVec_or, Int32.toBitVec_neg, Int32.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]
@[simp] theorem Int64.neg_one_or {a : Int64} : -1 ||| a = -1 := by
  rw [← Int64.toBitVec_inj, Int64.toBitVec_or, Int64.toBitVec_neg, Int64.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]
@[simp] theorem ISize.neg_one_or {a : ISize} : -1 ||| a = -1 := by
  rw [← ISize.toBitVec_inj, ISize.toBitVec_or, ISize.toBitVec_neg, ISize.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_or]

@[simp] theorem Int8.or_neg_one {a : Int8} : a ||| -1 = -1 := by rw [Int8.or_comm, neg_one_or]
@[simp] theorem Int16.or_neg_one {a : Int16} : a ||| -1 = -1 := by rw [Int16.or_comm, neg_one_or]
@[simp] theorem Int32.or_neg_one {a : Int32} : a ||| -1 = -1 := by rw [Int32.or_comm, neg_one_or]
@[simp] theorem Int64.or_neg_one {a : Int64} : a ||| -1 = -1 := by rw [Int64.or_comm, neg_one_or]
@[simp] theorem ISize.or_neg_one {a : ISize} : a ||| -1 = -1 := by rw [ISize.or_comm, neg_one_or]

@[simp] theorem Int8.or_eq_zero_iff {a b : Int8} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.or_eq_zero_iff {a b : Int16} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.or_eq_zero_iff {a b : Int32} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.or_eq_zero_iff {a b : Int64} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.or_eq_zero_iff {a b : ISize} : a ||| b = 0 ↔ a = 0 ∧ b = 0 := by
  simp [← ISize.toBitVec_inj]

protected theorem Int8.and_assoc (a b c : Int8) : a &&& b &&& c = a &&& (b &&& c) := Int8.toBitVec_inj.1 (BitVec.and_assoc _ _ _)
protected theorem Int16.and_assoc (a b c : Int16) : a &&& b &&& c = a &&& (b &&& c) := Int16.toBitVec_inj.1 (BitVec.and_assoc _ _ _)
protected theorem Int32.and_assoc (a b c : Int32) : a &&& b &&& c = a &&& (b &&& c) := Int32.toBitVec_inj.1 (BitVec.and_assoc _ _ _)
protected theorem Int64.and_assoc (a b c : Int64) : a &&& b &&& c = a &&& (b &&& c) := Int64.toBitVec_inj.1 (BitVec.and_assoc _ _ _)
protected theorem ISize.and_assoc (a b c : ISize) : a &&& b &&& c = a &&& (b &&& c) := ISize.toBitVec_inj.1 (BitVec.and_assoc _ _ _)

instance : Std.Associative (α := Int8) (· &&& ·) := ⟨Int8.and_assoc⟩
instance : Std.Associative (α := Int16) (· &&& ·) := ⟨Int16.and_assoc⟩
instance : Std.Associative (α := Int32) (· &&& ·) := ⟨Int32.and_assoc⟩
instance : Std.Associative (α := Int64) (· &&& ·) := ⟨Int64.and_assoc⟩
instance : Std.Associative (α := ISize) (· &&& ·) := ⟨ISize.and_assoc⟩

protected theorem Int8.and_comm (a b : Int8) : a &&& b = b &&& a := Int8.toBitVec_inj.1 (BitVec.and_comm _ _)
protected theorem Int16.and_comm (a b : Int16) : a &&& b = b &&& a := Int16.toBitVec_inj.1 (BitVec.and_comm _ _)
protected theorem Int32.and_comm (a b : Int32) : a &&& b = b &&& a := Int32.toBitVec_inj.1 (BitVec.and_comm _ _)
protected theorem Int64.and_comm (a b : Int64) : a &&& b = b &&& a := Int64.toBitVec_inj.1 (BitVec.and_comm _ _)
protected theorem ISize.and_comm (a b : ISize) : a &&& b = b &&& a := ISize.toBitVec_inj.1 (BitVec.and_comm _ _)

instance : Std.Commutative (α := Int8) (· &&& ·) := ⟨Int8.and_comm⟩
instance : Std.Commutative (α := Int16) (· &&& ·) := ⟨Int16.and_comm⟩
instance : Std.Commutative (α := Int32) (· &&& ·) := ⟨Int32.and_comm⟩
instance : Std.Commutative (α := Int64) (· &&& ·) := ⟨Int64.and_comm⟩
instance : Std.Commutative (α := ISize) (· &&& ·) := ⟨ISize.and_comm⟩

@[simp] protected theorem Int8.and_self {a : Int8} : a &&& a = a := Int8.toBitVec_inj.1 BitVec.and_self
@[simp] protected theorem Int16.and_self {a : Int16} : a &&& a = a := Int16.toBitVec_inj.1 BitVec.and_self
@[simp] protected theorem Int32.and_self {a : Int32} : a &&& a = a := Int32.toBitVec_inj.1 BitVec.and_self
@[simp] protected theorem Int64.and_self {a : Int64} : a &&& a = a := Int64.toBitVec_inj.1 BitVec.and_self
@[simp] protected theorem ISize.and_self {a : ISize} : a &&& a = a := ISize.toBitVec_inj.1 BitVec.and_self

instance : Std.IdempotentOp (α := Int8) (· &&& ·) := ⟨fun _ => Int8.and_self⟩
instance : Std.IdempotentOp (α := Int16) (· &&& ·) := ⟨fun _ => Int16.and_self⟩
instance : Std.IdempotentOp (α := Int32) (· &&& ·) := ⟨fun _ => Int32.and_self⟩
instance : Std.IdempotentOp (α := Int64) (· &&& ·) := ⟨fun _ => Int64.and_self⟩
instance : Std.IdempotentOp (α := ISize) (· &&& ·) := ⟨fun _ => ISize.and_self⟩

@[simp] protected theorem Int8.and_zero {a : Int8} : a &&& 0 = 0 := Int8.toBitVec_inj.1 BitVec.and_zero
@[simp] protected theorem Int16.and_zero {a : Int16} : a &&& 0 = 0 := Int16.toBitVec_inj.1 BitVec.and_zero
@[simp] protected theorem Int32.and_zero {a : Int32} : a &&& 0 = 0 := Int32.toBitVec_inj.1 BitVec.and_zero
@[simp] protected theorem Int64.and_zero {a : Int64} : a &&& 0 = 0 := Int64.toBitVec_inj.1 BitVec.and_zero
@[simp] protected theorem ISize.and_zero {a : ISize} : a &&& 0 = 0 := ISize.toBitVec_inj.1 BitVec.and_zero

@[simp] protected theorem Int8.zero_and {a : Int8} : 0 &&& a = 0 := Int8.toBitVec_inj.1 BitVec.zero_and
@[simp] protected theorem Int16.zero_and {a : Int16} : 0 &&& a = 0 := Int16.toBitVec_inj.1 BitVec.zero_and
@[simp] protected theorem Int32.zero_and {a : Int32} : 0 &&& a = 0 := Int32.toBitVec_inj.1 BitVec.zero_and
@[simp] protected theorem Int64.zero_and {a : Int64} : 0 &&& a = 0 := Int64.toBitVec_inj.1 BitVec.zero_and
@[simp] protected theorem ISize.zero_and {a : ISize} : 0 &&& a = 0 := ISize.toBitVec_inj.1 BitVec.zero_and

@[simp] theorem Int8.neg_one_and {a : Int8} : -1 &&& a = a := by
  rw [← Int8.toBitVec_inj, Int8.toBitVec_and, Int8.toBitVec_neg, Int8.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]
@[simp] theorem Int16.neg_one_and {a : Int16} : -1 &&& a = a := by
  rw [← Int16.toBitVec_inj, Int16.toBitVec_and, Int16.toBitVec_neg, Int16.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]
@[simp] theorem Int32.neg_one_and {a : Int32} : -1 &&& a = a := by
  rw [← Int32.toBitVec_inj, Int32.toBitVec_and, Int32.toBitVec_neg, Int32.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]
@[simp] theorem Int64.neg_one_and {a : Int64} : -1 &&& a = a := by
  rw [← Int64.toBitVec_inj, Int64.toBitVec_and, Int64.toBitVec_neg, Int64.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]
@[simp] theorem ISize.neg_one_and {a : ISize} : -1 &&& a = a := by
  rw [← ISize.toBitVec_inj, ISize.toBitVec_and, ISize.toBitVec_neg, ISize.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_and]

@[simp] theorem Int8.and_neg_one {a : Int8} : a &&& -1 = a := by rw [Int8.and_comm, neg_one_and]
@[simp] theorem Int16.and_neg_one {a : Int16} : a &&& -1 = a := by rw [Int16.and_comm, neg_one_and]
@[simp] theorem Int32.and_neg_one {a : Int32} : a &&& -1 = a := by rw [Int32.and_comm, neg_one_and]
@[simp] theorem Int64.and_neg_one {a : Int64} : a &&& -1 = a := by rw [Int64.and_comm, neg_one_and]
@[simp] theorem ISize.and_neg_one {a : ISize} : a &&& -1 = a := by rw [ISize.and_comm, neg_one_and]

instance : Std.LawfulCommIdentity (α := Int8) (· &&& ·) (-1) where
  right_id _ := Int8.and_neg_one
instance : Std.LawfulCommIdentity (α := Int16) (· &&& ·) (-1) where
  right_id _ := Int16.and_neg_one
instance : Std.LawfulCommIdentity (α := Int32) (· &&& ·) (-1) where
  right_id _ := Int32.and_neg_one
instance : Std.LawfulCommIdentity (α := Int64) (· &&& ·) (-1) where
  right_id _ := Int64.and_neg_one
instance : Std.LawfulCommIdentity (α := ISize) (· &&& ·) (-1) where
  right_id _ := ISize.and_neg_one

@[simp] theorem Int8.and_eq_neg_one_iff {a b : Int8} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← Int8.toBitVec_inj, Int8.toBitVec_and, Int8.toBitVec_neg, Int8.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]
@[simp] theorem Int16.and_eq_neg_one_iff {a b : Int16} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← Int16.toBitVec_inj, Int16.toBitVec_and, Int16.toBitVec_neg, Int16.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]
@[simp] theorem Int32.and_eq_neg_one_iff {a b : Int32} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← Int32.toBitVec_inj, Int32.toBitVec_and, Int32.toBitVec_neg, Int32.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]
@[simp] theorem Int64.and_eq_neg_one_iff {a b : Int64} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← Int64.toBitVec_inj, Int64.toBitVec_and, Int64.toBitVec_neg, Int64.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]
@[simp] theorem ISize.and_eq_neg_one_iff {a b : ISize} : a &&& b = -1 ↔ a = -1 ∧ b = -1 := by
  simp only [← ISize.toBitVec_inj, ISize.toBitVec_and, ISize.toBitVec_neg, ISize.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.and_eq_allOnes_iff]

protected theorem Int8.xor_assoc (a b c : Int8) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := Int8.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)
protected theorem Int16.xor_assoc (a b c : Int16) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := Int16.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)
protected theorem Int32.xor_assoc (a b c : Int32) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := Int32.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)
protected theorem Int64.xor_assoc (a b c : Int64) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := Int64.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)
protected theorem ISize.xor_assoc (a b c : ISize) : a ^^^ b ^^^ c = a ^^^ (b ^^^ c) := ISize.toBitVec_inj.1 (BitVec.xor_assoc _ _ _)

instance : Std.Associative (α := Int8) (· ^^^ ·) := ⟨Int8.xor_assoc⟩
instance : Std.Associative (α := Int16) (· ^^^ ·) := ⟨Int16.xor_assoc⟩
instance : Std.Associative (α := Int32) (· ^^^ ·) := ⟨Int32.xor_assoc⟩
instance : Std.Associative (α := Int64) (· ^^^ ·) := ⟨Int64.xor_assoc⟩
instance : Std.Associative (α := ISize) (· ^^^ ·) := ⟨ISize.xor_assoc⟩

protected theorem Int8.xor_comm (a b : Int8) : a ^^^ b = b ^^^ a := Int8.toBitVec_inj.1 (BitVec.xor_comm _ _)
protected theorem Int16.xor_comm (a b : Int16) : a ^^^ b = b ^^^ a := Int16.toBitVec_inj.1 (BitVec.xor_comm _ _)
protected theorem Int32.xor_comm (a b : Int32) : a ^^^ b = b ^^^ a := Int32.toBitVec_inj.1 (BitVec.xor_comm _ _)
protected theorem Int64.xor_comm (a b : Int64) : a ^^^ b = b ^^^ a := Int64.toBitVec_inj.1 (BitVec.xor_comm _ _)
protected theorem ISize.xor_comm (a b : ISize) : a ^^^ b = b ^^^ a := ISize.toBitVec_inj.1 (BitVec.xor_comm _ _)

instance : Std.Commutative (α := Int8) (· ^^^ ·) := ⟨Int8.xor_comm⟩
instance : Std.Commutative (α := Int16) (· ^^^ ·) := ⟨Int16.xor_comm⟩
instance : Std.Commutative (α := Int32) (· ^^^ ·) := ⟨Int32.xor_comm⟩
instance : Std.Commutative (α := Int64) (· ^^^ ·) := ⟨Int64.xor_comm⟩
instance : Std.Commutative (α := ISize) (· ^^^ ·) := ⟨ISize.xor_comm⟩

@[simp] protected theorem Int8.xor_self {a : Int8} : a ^^^ a = 0 := Int8.toBitVec_inj.1 BitVec.xor_self
@[simp] protected theorem Int16.xor_self {a : Int16} : a ^^^ a = 0 := Int16.toBitVec_inj.1 BitVec.xor_self
@[simp] protected theorem Int32.xor_self {a : Int32} : a ^^^ a = 0 := Int32.toBitVec_inj.1 BitVec.xor_self
@[simp] protected theorem Int64.xor_self {a : Int64} : a ^^^ a = 0 := Int64.toBitVec_inj.1 BitVec.xor_self
@[simp] protected theorem ISize.xor_self {a : ISize} : a ^^^ a = 0 := ISize.toBitVec_inj.1 BitVec.xor_self

@[simp] protected theorem Int8.xor_zero {a : Int8} : a ^^^ 0 = a := Int8.toBitVec_inj.1 BitVec.xor_zero
@[simp] protected theorem Int16.xor_zero {a : Int16} : a ^^^ 0 = a := Int16.toBitVec_inj.1 BitVec.xor_zero
@[simp] protected theorem Int32.xor_zero {a : Int32} : a ^^^ 0 = a := Int32.toBitVec_inj.1 BitVec.xor_zero
@[simp] protected theorem Int64.xor_zero {a : Int64} : a ^^^ 0 = a := Int64.toBitVec_inj.1 BitVec.xor_zero
@[simp] protected theorem ISize.xor_zero {a : ISize} : a ^^^ 0 = a := ISize.toBitVec_inj.1 BitVec.xor_zero

@[simp] protected theorem Int8.zero_xor {a : Int8} : 0 ^^^ a = a := Int8.toBitVec_inj.1 BitVec.zero_xor
@[simp] protected theorem Int16.zero_xor {a : Int16} : 0 ^^^ a = a := Int16.toBitVec_inj.1 BitVec.zero_xor
@[simp] protected theorem Int32.zero_xor {a : Int32} : 0 ^^^ a = a := Int32.toBitVec_inj.1 BitVec.zero_xor
@[simp] protected theorem Int64.zero_xor {a : Int64} : 0 ^^^ a = a := Int64.toBitVec_inj.1 BitVec.zero_xor
@[simp] protected theorem ISize.zero_xor {a : ISize} : 0 ^^^ a = a := ISize.toBitVec_inj.1 BitVec.zero_xor

@[simp] theorem Int8.neg_one_xor {a : Int8} : -1 ^^^ a = ~~~a := by
  rw [← Int8.toBitVec_inj, Int8.toBitVec_xor, Int8.toBitVec_neg, Int8.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, Int8.toBitVec_not]
@[simp] theorem Int16.neg_one_xor {a : Int16} : -1 ^^^ a = ~~~a := by
  rw [← Int16.toBitVec_inj, Int16.toBitVec_xor, Int16.toBitVec_neg, Int16.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, Int16.toBitVec_not]
@[simp] theorem Int32.neg_one_xor {a : Int32} : -1 ^^^ a = ~~~a := by
  rw [← Int32.toBitVec_inj, Int32.toBitVec_xor, Int32.toBitVec_neg, Int32.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, Int32.toBitVec_not]
@[simp] theorem Int64.neg_one_xor {a : Int64} : -1 ^^^ a = ~~~a := by
  rw [← Int64.toBitVec_inj, Int64.toBitVec_xor, Int64.toBitVec_neg, Int64.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, Int64.toBitVec_not]
@[simp] theorem ISize.neg_one_xor {a : ISize} : -1 ^^^ a = ~~~a := by
  rw [← ISize.toBitVec_inj, ISize.toBitVec_xor, ISize.toBitVec_neg, ISize.toBitVec_one,
    BitVec.neg_one_eq_allOnes, BitVec.allOnes_xor, ISize.toBitVec_not]

@[simp] theorem Int8.xor_neg_one {a : Int8} : a ^^^ -1 = ~~~a := by rw [Int8.xor_comm, neg_one_xor]
@[simp] theorem Int16.xor_neg_one {a : Int16} : a ^^^ -1 = ~~~a := by rw [Int16.xor_comm, neg_one_xor]
@[simp] theorem Int32.xor_neg_one {a : Int32} : a ^^^ -1 = ~~~a := by rw [Int32.xor_comm, neg_one_xor]
@[simp] theorem Int64.xor_neg_one {a : Int64} : a ^^^ -1 = ~~~a := by rw [Int64.xor_comm, neg_one_xor]
@[simp] theorem ISize.xor_neg_one {a : ISize} : a ^^^ -1 = ~~~a := by rw [ISize.xor_comm, neg_one_xor]

instance : Std.LawfulCommIdentity (α := Int8) (· ^^^ ·) 0 where
  right_id _ := Int8.xor_zero
instance : Std.LawfulCommIdentity (α := Int16) (· ^^^ ·) 0  where
  right_id _ := Int16.xor_zero
instance : Std.LawfulCommIdentity (α := Int32) (· ^^^ ·) 0 where
  right_id _ := Int32.xor_zero
instance : Std.LawfulCommIdentity (α := Int64) (· ^^^ ·) 0 where
  right_id _ := Int64.xor_zero
instance : Std.LawfulCommIdentity (α := ISize) (· ^^^ ·) 0 where
  right_id _ := ISize.xor_zero

@[simp] theorem Int8.xor_eq_zero_iff {a b : Int8} : a ^^^ b = 0 ↔ a = b := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.xor_eq_zero_iff {a b : Int16} : a ^^^ b = 0 ↔ a = b := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.xor_eq_zero_iff {a b : Int32} : a ^^^ b = 0 ↔ a = b := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.xor_eq_zero_iff {a b : Int64} : a ^^^ b = 0 ↔ a = b := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.xor_eq_zero_iff {a b : ISize} : a ^^^ b = 0 ↔ a = b := by simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.xor_left_inj {a b : Int8} (c : Int8) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.xor_left_inj {a b : Int16} (c : Int16) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.xor_left_inj {a b : Int32} (c : Int32) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.xor_left_inj {a b : Int64} (c : Int64) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.xor_left_inj {a b : ISize} (c : ISize) : (a ^^^ c = b ^^^ c) ↔ a = b := by
  simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.xor_right_inj {a b : Int8} (c : Int8) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.xor_right_inj {a b : Int16} (c : Int16) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.xor_right_inj {a b : Int32} (c : Int32) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.xor_right_inj {a b : Int64} (c : Int64) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.xor_right_inj {a b : ISize} (c : ISize) : (c ^^^ a = c ^^^ b) ↔ a = b := by
  simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.not_zero : ~~~(0 : Int8) = -1 := rfl
@[simp] theorem Int16.not_zero : ~~~(0 : Int16) = -1 := rfl
@[simp] theorem Int32.not_zero : ~~~(0 : Int32) = -1 := rfl
@[simp] theorem Int64.not_zero : ~~~(0 : Int64) = -1 := rfl
@[simp] theorem ISize.not_zero : ~~~(0 : ISize) = -1 := by simp [ISize.not_eq_neg_sub]

@[simp] theorem Int8.not_neg_one : ~~~(-1 : Int8) = 0 := rfl
@[simp] theorem Int16.not_neg_one : ~~~(-1 : Int16) = 0 := rfl
@[simp] theorem Int32.not_neg_one : ~~~(-1 : Int32) = 0 := rfl
@[simp] theorem Int64.not_neg_one : ~~~(-1 : Int64) = 0 := rfl
@[simp] theorem ISize.not_neg_one : ~~~(-1 : ISize) = 0 := by simp [ISize.not_eq_neg_sub]

@[simp] theorem Int8.not_not {a : Int8} : ~~~(~~~a) = a := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.not_not {a : Int16} : ~~~(~~~a) = a := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.not_not {a : Int32} : ~~~(~~~a) = a := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.not_not {a : Int64} : ~~~(~~~a) = a := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.not_not {a : ISize} : ~~~(~~~a) = a := by simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.not_inj {a b : Int8} : ~~~a = ~~~b ↔ a = b := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.not_inj {a b : Int16} : ~~~a = ~~~b ↔ a = b := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.not_inj {a b : Int32} : ~~~a = ~~~b ↔ a = b := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.not_inj {a b : Int64} : ~~~a = ~~~b ↔ a = b := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.not_inj {a b : ISize} : ~~~a = ~~~b ↔ a = b := by simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.and_not_self {a : Int8} : a &&& ~~~a = 0 := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.and_not_self {a : Int16} : a &&& ~~~a = 0 := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.and_not_self {a : Int32} : a &&& ~~~a = 0 := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.and_not_self {a : Int64} : a &&& ~~~a = 0 := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.and_not_self {a : ISize} : a &&& ~~~a = 0 := by simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.not_and_self {a : Int8} : ~~~a &&& a = 0 := by simp [Int8.and_comm]
@[simp] theorem Int16.not_and_self {a : Int16} : ~~~a &&& a = 0 := by simp [Int16.and_comm]
@[simp] theorem Int32.not_and_self {a : Int32} : ~~~a &&& a = 0 := by simp [Int32.and_comm]
@[simp] theorem Int64.not_and_self {a : Int64} : ~~~a &&& a = 0 := by simp [Int64.and_comm]
@[simp] theorem ISize.not_and_self {a : ISize} : ~~~a &&& a = 0 := by simp [ISize.and_comm]

@[simp] theorem Int8.or_not_self {a : Int8} : a ||| ~~~a = -1 := by
  rw [← Int8.toBitVec_inj, Int8.toBitVec_or, Int8.toBitVec_not, BitVec.or_not_self,
    Int8.toBitVec_neg, Int8.toBitVec_one, BitVec.neg_one_eq_allOnes]
@[simp] theorem Int16.or_not_self {a : Int16} : a ||| ~~~a = -1 := by
  rw [← Int16.toBitVec_inj, Int16.toBitVec_or, Int16.toBitVec_not, BitVec.or_not_self,
    Int16.toBitVec_neg, Int16.toBitVec_one, BitVec.neg_one_eq_allOnes]
@[simp] theorem Int32.or_not_self {a : Int32} : a ||| ~~~a = -1 := by
  rw [← Int32.toBitVec_inj, Int32.toBitVec_or, Int32.toBitVec_not, BitVec.or_not_self,
    Int32.toBitVec_neg, Int32.toBitVec_one, BitVec.neg_one_eq_allOnes]
@[simp] theorem Int64.or_not_self {a : Int64} : a ||| ~~~a = -1 := by
  rw [← Int64.toBitVec_inj, Int64.toBitVec_or, Int64.toBitVec_not, BitVec.or_not_self,
    Int64.toBitVec_neg, Int64.toBitVec_one, BitVec.neg_one_eq_allOnes]
@[simp] theorem ISize.or_not_self {a : ISize} : a ||| ~~~a = -1 := by
  rw [← ISize.toBitVec_inj, ISize.toBitVec_or, ISize.toBitVec_not, BitVec.or_not_self,
    ISize.toBitVec_neg, ISize.toBitVec_one, BitVec.neg_one_eq_allOnes]

@[simp] theorem Int8.not_or_self {a : Int8} : ~~~a ||| a = -1 := by simp [Int8.or_comm]
@[simp] theorem Int16.not_or_self {a : Int16} : ~~~a ||| a = -1 := by simp [Int16.or_comm]
@[simp] theorem Int32.not_or_self {a : Int32} : ~~~a ||| a = -1 := by simp [Int32.or_comm]
@[simp] theorem Int64.not_or_self {a : Int64} : ~~~a ||| a = -1 := by simp [Int64.or_comm]
@[simp] theorem ISize.not_or_self {a : ISize} : ~~~a ||| a = -1 := by simp [ISize.or_comm]

theorem Int8.not_eq_comm {a b : Int8} : ~~~a = b ↔ a = ~~~b := by
  simp [← Int8.toBitVec_inj, BitVec.not_eq_comm]
theorem Int16.not_eq_comm {a b : Int16} : ~~~a = b ↔ a = ~~~b := by
  simp [← Int16.toBitVec_inj, BitVec.not_eq_comm]
theorem Int32.not_eq_comm {a b : Int32} : ~~~a = b ↔ a = ~~~b := by
  simp [← Int32.toBitVec_inj, BitVec.not_eq_comm]
theorem Int64.not_eq_comm {a b : Int64} : ~~~a = b ↔ a = ~~~b := by
  simp [← Int64.toBitVec_inj, BitVec.not_eq_comm]
theorem ISize.not_eq_comm {a b : ISize} : ~~~a = b ↔ a = ~~~b := by
  simp [← ISize.toBitVec_inj, BitVec.not_eq_comm]

@[simp] theorem Int8.ne_not_self {a : Int8} : a ≠ ~~~a := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.ne_not_self {a : Int16} : a ≠ ~~~a := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.ne_not_self {a : Int32} : a ≠ ~~~a := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.ne_not_self {a : Int64} : a ≠ ~~~a := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.ne_not_self {a : ISize} : a ≠ ~~~a := by simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.not_ne_self {a : Int8} : ~~~a ≠ a := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.not_ne_self {a : Int16} : ~~~a ≠ a := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.not_ne_self {a : Int32} : ~~~a ≠ a := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.not_ne_self {a : Int64} : ~~~a ≠ a := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.not_ne_self {a : ISize} : ~~~a ≠ a := by simp [← ISize.toBitVec_inj]

theorem Int8.not_xor {a b : Int8} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← Int8.toBitVec_inj, BitVec.not_xor_left]
theorem Int16.not_xor {a b : Int16} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← Int16.toBitVec_inj, BitVec.not_xor_left]
theorem Int32.not_xor {a b : Int32} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← Int32.toBitVec_inj, BitVec.not_xor_left]
theorem Int64.not_xor {a b : Int64} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← Int64.toBitVec_inj, BitVec.not_xor_left]
theorem ISize.not_xor {a b : ISize} : ~~~a ^^^ b = ~~~(a ^^^ b) := by
  simp [← ISize.toBitVec_inj, BitVec.not_xor_left]

theorem Int8.xor_not {a b : Int8} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← Int8.toBitVec_inj, BitVec.not_xor_right]
theorem Int16.xor_not {a b : Int16} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← Int16.toBitVec_inj, BitVec.not_xor_right]
theorem Int32.xor_not {a b : Int32} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← Int32.toBitVec_inj, BitVec.not_xor_right]
theorem Int64.xor_not {a b : Int64} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← Int64.toBitVec_inj, BitVec.not_xor_right]
theorem ISize.xor_not {a b : ISize} : a ^^^ ~~~b = ~~~(a ^^^ b) := by
  simp [← ISize.toBitVec_inj, BitVec.not_xor_right]

@[simp] theorem Int8.shiftLeft_zero {a : Int8} : a <<< 0 = a := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.shiftLeft_zero {a : Int16} : a <<< 0 = a := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.shiftLeft_zero {a : Int32} : a <<< 0 = a := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.shiftLeft_zero {a : Int64} : a <<< 0 = a := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.shiftLeft_zero {a : ISize} : a <<< 0 = a := by simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.zero_shiftLeft {a : Int8} : 0 <<< a = 0 := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.zero_shiftLeft {a : Int16} : 0 <<< a = 0 := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.zero_shiftLeft {a : Int32} : 0 <<< a = 0 := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.zero_shiftLeft {a : Int64} : 0 <<< a = 0 := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.zero_shiftLeft {a : ISize} : 0 <<< a = 0 := by simp [← ISize.toBitVec_inj]

theorem Int8.shiftLeft_xor {a b c : Int8} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← Int8.toBitVec_inj, BitVec.shiftLeft_xor_distrib]
theorem Int16.shiftLeft_xor {a b c : Int16} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← Int16.toBitVec_inj, BitVec.shiftLeft_xor_distrib]
theorem Int32.shiftLeft_xor {a b c : Int32} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← Int32.toBitVec_inj, BitVec.shiftLeft_xor_distrib]
theorem Int64.shiftLeft_xor {a b c : Int64} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← Int64.toBitVec_inj, BitVec.shiftLeft_xor_distrib]
theorem ISize.shiftLeft_xor {a b c : ISize} : (a ^^^ b) <<< c = (a <<< c) ^^^ (b <<< c) := by
  simp [← ISize.toBitVec_inj, BitVec.shiftLeft_xor_distrib]

theorem Int8.shiftLeft_and {a b c : Int8} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← Int8.toBitVec_inj, BitVec.shiftLeft_and_distrib]
theorem Int16.shiftLeft_and {a b c : Int16} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← Int16.toBitVec_inj, BitVec.shiftLeft_and_distrib]
theorem Int32.shiftLeft_and {a b c : Int32} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← Int32.toBitVec_inj, BitVec.shiftLeft_and_distrib]
theorem Int64.shiftLeft_and {a b c : Int64} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← Int64.toBitVec_inj, BitVec.shiftLeft_and_distrib]
theorem ISize.shiftLeft_and {a b c : ISize} : (a &&& b) <<< c = (a <<< c) &&& (b <<< c) := by
  simp [← ISize.toBitVec_inj, BitVec.shiftLeft_and_distrib]

theorem Int8.shiftLeft_or {a b c : Int8} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← Int8.toBitVec_inj, BitVec.shiftLeft_or_distrib]
theorem Int16.shiftLeft_or {a b c : Int16} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← Int16.toBitVec_inj, BitVec.shiftLeft_or_distrib]
theorem Int32.shiftLeft_or {a b c : Int32} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← Int32.toBitVec_inj, BitVec.shiftLeft_or_distrib]
theorem Int64.shiftLeft_or {a b c : Int64} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← Int64.toBitVec_inj, BitVec.shiftLeft_or_distrib]
theorem ISize.shiftLeft_or {a b c : ISize} : (a ||| b) <<< c = (a <<< c) ||| (b <<< c) := by
  simp [← ISize.toBitVec_inj, BitVec.shiftLeft_or_distrib]

@[simp] theorem Int8.neg_one_shiftLeft_and_shiftLeft {a b : Int8} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← Int8.shiftLeft_and]
@[simp] theorem Int16.neg_one_shiftLeft_and_shiftLeft {a b : Int16} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← Int16.shiftLeft_and]
@[simp] theorem Int32.neg_one_shiftLeft_and_shiftLeft {a b : Int32} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← Int32.shiftLeft_and]
@[simp] theorem Int64.neg_one_shiftLeft_and_shiftLeft {a b : Int64} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← Int64.shiftLeft_and]
@[simp] theorem ISize.neg_one_shiftLeft_and_shiftLeft {a b : ISize} :
    (-1) <<< b &&& a <<< b = a <<< b := by simp [← ISize.shiftLeft_and]

@[simp] theorem Int8.neg_one_shiftLeft_or_shiftLeft {a b : Int8} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← Int8.shiftLeft_or]
@[simp] theorem Int16.neg_one_shiftLeft_or_shiftLeft {a b : Int16} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← Int16.shiftLeft_or]
@[simp] theorem Int32.neg_one_shiftLeft_or_shiftLeft {a b : Int32} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← Int32.shiftLeft_or]
@[simp] theorem Int64.neg_one_shiftLeft_or_shiftLeft {a b : Int8} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← Int64.shiftLeft_or]
@[simp] theorem ISize.neg_one_shiftLeft_or_shiftLeft {a b : ISize} :
    (-1) <<< b ||| a <<< b = (-1) <<< b := by simp [← ISize.shiftLeft_or]

@[simp] theorem Int8.shiftRight_zero {a : Int8} : a >>> 0 = a := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.shiftRight_zero {a : Int16} : a >>> 0 = a := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.shiftRight_zero {a : Int32} : a >>> 0 = a := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.shiftRight_zero {a : Int64} : a >>> 0 = a := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.shiftRight_zero {a : ISize} : a >>> 0 = a := by simp [← ISize.toBitVec_inj]

@[simp] theorem Int8.zero_shiftRight {a : Int8} : 0 >>> a = 0 := by simp [← Int8.toBitVec_inj]
@[simp] theorem Int16.zero_shiftRight {a : Int16} : 0 >>> a = 0 := by simp [← Int16.toBitVec_inj]
@[simp] theorem Int32.zero_shiftRight {a : Int32} : 0 >>> a = 0 := by simp [← Int32.toBitVec_inj]
@[simp] theorem Int64.zero_shiftRight {a : Int64} : 0 >>> a = 0 := by simp [← Int64.toBitVec_inj]
@[simp] theorem ISize.zero_shiftRight {a : ISize} : 0 >>> a = 0 := by simp [← ISize.toBitVec_inj]

theorem Int8.shiftRight_xor {a b c : Int8} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← Int8.toBitVec_inj, BitVec.sshiftRight_xor_distrib]
theorem Int16.shiftRight_xor {a b c : Int16} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← Int16.toBitVec_inj, BitVec.sshiftRight_xor_distrib]
theorem Int32.shiftRight_xor {a b c : Int32} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← Int32.toBitVec_inj, BitVec.sshiftRight_xor_distrib]
theorem Int64.shiftRight_xor {a b c : Int64} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← Int64.toBitVec_inj, BitVec.sshiftRight_xor_distrib]
theorem ISize.shiftRight_xor {a b c : ISize} : (a ^^^ b) >>> c = (a >>> c) ^^^ (b >>> c) := by
  simp [← ISize.toBitVec_inj, BitVec.sshiftRight_xor_distrib]

theorem Int8.shiftRight_and {a b c : Int8} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← Int8.toBitVec_inj, BitVec.sshiftRight_and_distrib]
theorem Int16.shiftRight_and {a b c : Int16} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← Int16.toBitVec_inj, BitVec.sshiftRight_and_distrib]
theorem Int32.shiftRight_and {a b c : Int32} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← Int32.toBitVec_inj, BitVec.sshiftRight_and_distrib]
theorem Int64.shiftRight_and {a b c : Int64} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← Int64.toBitVec_inj, BitVec.sshiftRight_and_distrib]
theorem ISize.shiftRight_and {a b c : ISize} : (a &&& b) >>> c = (a >>> c) &&& (b >>> c) := by
  simp [← ISize.toBitVec_inj, BitVec.sshiftRight_and_distrib]

theorem Int8.shiftRight_or {a b c : Int8} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← Int8.toBitVec_inj, BitVec.sshiftRight_or_distrib]
theorem Int16.shiftRight_or {a b c : Int16} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← Int16.toBitVec_inj, BitVec.sshiftRight_or_distrib]
theorem Int32.shiftRight_or {a b c : Int32} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← Int32.toBitVec_inj, BitVec.sshiftRight_or_distrib]
theorem Int64.shiftRight_or {a b c : Int64} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← Int64.toBitVec_inj, BitVec.sshiftRight_or_distrib]
theorem ISize.shiftRight_or {a b c : ISize} : (a ||| b) >>> c = (a >>> c) ||| (b >>> c) := by
  simp [← ISize.toBitVec_inj, BitVec.sshiftRight_or_distrib]
