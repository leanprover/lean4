/-
Copyright (c) 2024 Lean FRO, LLC. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.UInt.Basic
import Init.Data.Fin.Bitwise
import Init.Data.BitVec.Lemmas

set_option hygiene false in
macro "declare_bitwise_uint_theorems" typeName:ident bits:term:arg : command =>
let toNat_and := Lean.mkIdentFrom typeName (typeName.getId.modifyBase (·.str "toNat_and"))
`(
namespace $typeName

@[simp] protected theorem toNat_and (a b : $typeName) : (a &&& b).toNat = a.toNat &&& b.toNat := BitVec.toNat_and ..
@[simp] protected theorem toNat_or (a b : $typeName) : (a ||| b).toNat = a.toNat ||| b.toNat := BitVec.toNat_or ..
@[simp] protected theorem toNat_xor (a b : $typeName) : (a ^^^ b).toNat = a.toNat ^^^ b.toNat := BitVec.toNat_xor ..
@[simp] protected theorem toNat_shiftLeft (a b : $typeName) : (a <<< b).toNat = a.toNat <<< (b.toNat % $bits) % 2 ^ $bits := BitVec.toNat_shiftLeft
@[simp] protected theorem toNat_shiftRight (a b : $typeName) : (a >>> b).toNat = a.toNat >>> (b.toNat % $bits) := BitVec.toNat_ushiftRight ..

@[deprecated $toNat_and (since := "2024-11-23")] protected theorem and_toNat (a b : $typeName) : (a &&& b).toNat = a.toNat &&& b.toNat := BitVec.toNat_and ..

end $typeName
)

declare_bitwise_uint_theorems UInt8 8
declare_bitwise_uint_theorems UInt16 16
declare_bitwise_uint_theorems UInt32 32
declare_bitwise_uint_theorems UInt64 64
declare_bitwise_uint_theorems USize System.Platform.numBits
