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

@[simp] theorem UInt8.toInt8_add (a b : UInt8) : (a + b).toInt8 = a.toInt8 + b.toInt8 := rfl
@[simp] theorem UInt16.toInt16_add (a b : UInt16) : (a + b).toInt16 = a.toInt16 + b.toInt16 := rfl
@[simp] theorem UInt32.toInt32_add (a b : UInt32) : (a + b).toInt32 = a.toInt32 + b.toInt32 := rfl
@[simp] theorem UInt64.toInt64_add (a b : UInt64) : (a + b).toInt64 = a.toInt64 + b.toInt64 := rfl
@[simp] theorem USize.toISize_add (a b : USize) : (a + b).toISize = a.toISize + b.toISize := rfl

@[simp] theorem UInt8.toInt8_neg (a : UInt8) : (-a).toInt8 = -a.toInt8 := rfl
@[simp] theorem UInt16.toInt16_neg (a : UInt16) : (-a).toInt16 = -a.toInt16 := rfl
@[simp] theorem UInt32.toInt32_neg (a : UInt32) : (-a).toInt32 = -a.toInt32 := rfl
@[simp] theorem UInt64.toInt64_neg (a : UInt64) : (-a).toInt64 = -a.toInt64 := rfl
@[simp] theorem USize.toISize_neg (a : USize) : (-a).toISize = -a.toISize := rfl

@[simp] theorem UInt8.toInt8_sub (a b : UInt8) : (a - b).toInt8 = a.toInt8 - b.toInt8 := rfl
@[simp] theorem UInt16.toInt16_sub (a b : UInt16) : (a - b).toInt16 = a.toInt16 - b.toInt16 := rfl
@[simp] theorem UInt32.toInt32_sub (a b : UInt32) : (a - b).toInt32 = a.toInt32 - b.toInt32 := rfl
@[simp] theorem UInt64.toInt64_sub (a b : UInt64) : (a - b).toInt64 = a.toInt64 - b.toInt64 := rfl
@[simp] theorem USize.toISize_sub (a b : USize) : (a - b).toISize = a.toISize - b.toISize := rfl

@[simp] theorem UInt8.toInt8_mul (a b : UInt8) : (a * b).toInt8 = a.toInt8 * b.toInt8 := rfl
@[simp] theorem UInt16.toInt16_mul (a b : UInt16) : (a * b).toInt16 = a.toInt16 * b.toInt16 := rfl
@[simp] theorem UInt32.toInt32_mul (a b : UInt32) : (a * b).toInt32 = a.toInt32 * b.toInt32 := rfl
@[simp] theorem UInt64.toInt64_mul (a b : UInt64) : (a * b).toInt64 = a.toInt64 * b.toInt64 := rfl
@[simp] theorem USize.toISize_mul (a b : USize) : (a * b).toISize = a.toISize * b.toISize := rfl

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

@[simp] theorem Int8.toUInt8_add (a b : Int8) : (a + b).toUInt8 = a.toUInt8 + b.toUInt8 := rfl
@[simp] theorem Int16.toUInt16_add (a b : Int16) : (a + b).toUInt16 = a.toUInt16 + b.toUInt16 := rfl
@[simp] theorem Int32.toUInt32_add (a b : Int32) : (a + b).toUInt32 = a.toUInt32 + b.toUInt32 := rfl
@[simp] theorem Int64.toUInt64_add (a b : Int64) : (a + b).toUInt64 = a.toUInt64 + b.toUInt64 := rfl
@[simp] theorem ISize.toUSize_add (a b : ISize) : (a + b).toUSize = a.toUSize + b.toUSize := rfl

@[simp] theorem Int8.toUInt8_neg (a : Int8) : (-a).toUInt8 = -a.toUInt8 := rfl
@[simp] theorem Int16.toUInt16_neg (a : Int16) : (-a).toUInt16 = -a.toUInt16 := rfl
@[simp] theorem Int32.toUInt32_neg (a : Int32) : (-a).toUInt32 = -a.toUInt32 := rfl
@[simp] theorem Int64.toUInt64_neg (a : Int64) : (-a).toUInt64 = -a.toUInt64 := rfl
@[simp] theorem ISize.toUSize_neg (a : ISize) : (-a).toUSize = -a.toUSize := rfl

@[simp] theorem Int8.toUInt8_sub (a b : Int8) : (a - b).toUInt8 = a.toUInt8 - b.toUInt8 := rfl
@[simp] theorem Int16.toUInt16_sub (a b : Int16) : (a - b).toUInt16 = a.toUInt16 - b.toUInt16 := rfl
@[simp] theorem Int32.toUInt32_sub (a b : Int32) : (a - b).toUInt32 = a.toUInt32 - b.toUInt32 := rfl
@[simp] theorem Int64.toUInt64_sub (a b : Int64) : (a - b).toUInt64 = a.toUInt64 - b.toUInt64 := rfl
@[simp] theorem ISize.toUSize_sub (a b : ISize) : (a - b).toUSize = a.toUSize - b.toUSize := rfl

@[simp] theorem Int8.toUInt8_mul (a b : Int8) : (a * b).toUInt8 = a.toUInt8 * b.toUInt8 := rfl
@[simp] theorem Int16.toUInt16_mul (a b : Int16) : (a * b).toUInt16 = a.toUInt16 * b.toUInt16 := rfl
@[simp] theorem Int32.toUInt32_mul (a b : Int32) : (a * b).toUInt32 = a.toUInt32 * b.toUInt32 := rfl
@[simp] theorem Int64.toUInt64_mul (a b : Int64) : (a * b).toUInt64 = a.toUInt64 * b.toUInt64 := rfl
@[simp] theorem ISize.toUSize_mul (a b : ISize) : (a * b).toUSize = a.toUSize * b.toUSize := rfl

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
@[simp] theorem ISize.toInt_not (a : ISize) : (~~~a).toInt = (-a.toInt - 1).bmod (2 ^ System.Platform.numBits) := by simp [ISize.not_eq_neg_add]

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


-- We don't actually want bitwise theory about integers!

-- theorem BitVec.toInt_shiftLeft_eq_toInt {n : Nat} {x : BitVec w} : (x <<< n).toInt = (x.toInt * 2 ^ n).bmod (2 ^ w) := by
--   rw [toInt_shiftLeft, Nat.shiftLeft_eq, Int.natCast_mul, BitVec.toInt_eq_toNat_bmod,
--     Int.natCast_pow, Int.bmod_mul_bmod, Int.cast_ofNat_Int]

-- -- These are quite strange, I'm sure that more general statements are possible.
-- theorem BitVec.smod_ofNat_self (b : BitVec w) : (b.smod (BitVec.ofNat w w)).toNat = (b.toInt % w).toNat := sorry
-- theorem BitVec.smod_ofNat_self' (b : BitVec w) : (b.smod (OfNat.ofNat w)).toNat = (b.toInt % w).toNat := BitVec.smod_ofNat_self b
-- theorem BitVec.smod_natCast_self (b : BitVec w) : (b.smod (Nat.cast w)).toNat = (b.toInt % w).toNat := BitVec.smod_ofNat_self b

-- @[simp] theorem Int8.toInt_shiftLeft (a b : Int8) : (a <<< b).toInt = (a.toInt * (2 ^ (b.toInt % 8).toNat)).bmod (2 ^ 8) := by
--   rw [← toInt_toBitVec, Int8.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toInt_shiftLeft_eq_toInt,
--     toInt_toBitVec, BitVec.smod_ofNat_self', toInt_toBitVec]; simp
-- @[simp] theorem Int16.toInt_shiftLeft (a b : Int16) : (a <<< b).toInt = (a.toInt * (2 ^ (b.toInt % 16).toNat)).bmod (2 ^ 16) := by
--   rw [← toInt_toBitVec, Int16.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toInt_shiftLeft_eq_toInt,
--     toInt_toBitVec, BitVec.smod_ofNat_self', toInt_toBitVec]; simp
-- @[simp] theorem Int32.toInt_shiftLeft (a b : Int32) : (a <<< b).toInt = (a.toInt * (2 ^ (b.toInt % 32).toNat)).bmod (2 ^ 32) := by
--   rw [← toInt_toBitVec, Int32.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toInt_shiftLeft_eq_toInt,
--     toInt_toBitVec, BitVec.smod_ofNat_self', toInt_toBitVec]; simp
-- @[simp] theorem Int64.toInt_shiftLeft (a b : Int64) : (a <<< b).toInt = (a.toInt * (2 ^ (b.toInt % 64).toNat)).bmod (2 ^ 64) := by
--   rw [← toInt_toBitVec, Int64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toInt_shiftLeft_eq_toInt,
--     toInt_toBitVec, BitVec.smod_ofNat_self', toInt_toBitVec]; simp
-- @[simp] theorem ISize.toInt_shiftLeft (a b : ISize) : (a <<< b).toInt = (a.toInt * (2 ^ (b.toInt % System.Platform.numBits).toNat)).bmod (2 ^ System.Platform.numBits) := by
--   rw [← toInt_toBitVec, ISize.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.toInt_shiftLeft_eq_toInt,
--     toInt_toBitVec, BitVec.smod_natCast_self, toInt_toBitVec]

-- @[simp] theorem Int8.toInt_shiftRight (a b : Int8) : (a >>> b).toInt = a.toInt >>> (b.toInt % 8).toNat := by
--   rw [← toInt_toBitVec, Int8.toBitVec_shiftRight, BitVec.sshiftRight_eq',
--     BitVec.toInt_sshiftRight, BitVec.smod_ofNat_self']; simp
-- @[simp] theorem Int16.toInt_shiftRight (a b : Int16) : (a >>> b).toInt = a.toInt >>> (b.toInt % 16).toNat := by
--   rw [← toInt_toBitVec, Int16.toBitVec_shiftRight, BitVec.sshiftRight_eq',
--     BitVec.toInt_sshiftRight, BitVec.smod_ofNat_self']; simp
-- @[simp] theorem Int32.toInt_shiftRight (a b : Int32) : (a >>> b).toInt = a.toInt >>> (b.toInt % 32).toNat := by
--   rw [← toInt_toBitVec, Int32.toBitVec_shiftRight, BitVec.sshiftRight_eq',
--     BitVec.toInt_sshiftRight, BitVec.smod_ofNat_self']; simp
-- @[simp] theorem Int64.toInt_shiftRight (a b : Int64) : (a >>> b).toInt = a.toInt >>> (b.toInt % 64).toNat := by
--   rw [← toInt_toBitVec, Int64.toBitVec_shiftRight, BitVec.sshiftRight_eq',
--     BitVec.toInt_sshiftRight, BitVec.smod_ofNat_self']; simp
-- @[simp] theorem ISize.toInt_shiftRight (a b : ISize) : (a >>> b).toInt = a.toInt >>> (b.toInt % System.Platform.numBits).toNat := by
--   rw [← toInt_toBitVec, ISize.toBitVec_shiftRight, BitVec.sshiftRight_eq',
--     BitVec.toInt_sshiftRight, BitVec.smod_natCast_self, toInt_toBitVec, toInt_toBitVec]

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
  ISize.toInt_inj.1 (by simp)
