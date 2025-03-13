/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.SInt.Lemmas

set_option hygiene false in
macro "declare_bitwise_int_theorems" typeName:ident bits:term:arg : command =>
`(
namespace $typeName

@[simp, int_toBitVec] protected theorem toBitVec_add {a b : $typeName} : (a + b).toBitVec = a.toBitVec + b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_sub {a b : $typeName} : (a - b).toBitVec = a.toBitVec - b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_mul {a b : $typeName} : (a * b).toBitVec = a.toBitVec * b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_div {a b : $typeName} : (a / b).toBitVec = a.toBitVec.sdiv b.toBitVec := rfl
@[simp, int_toBitVec] protected theorem toBitVec_mod {a b : $typeName} : (a % b).toBitVec = a.toBitVec.srem b.toBitVec := rfl
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
