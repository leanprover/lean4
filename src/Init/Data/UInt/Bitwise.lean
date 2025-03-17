/-
Copyright (c) 2024 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Mac Malone
-/
prelude
import Init.Data.UInt.Lemmas
import Init.Data.Fin.Bitwise
import Init.Data.BitVec.Lemmas

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
