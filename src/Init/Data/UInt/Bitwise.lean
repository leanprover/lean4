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
macro "declare_bitwise_uint_theorems" typeName:ident : command =>
`(
namespace $typeName

@[simp] protected theorem and_toNat (a b : $typeName) : (a &&& b).toNat = a.toNat &&& b.toNat := BitVec.toNat_and ..

end $typeName
)

declare_bitwise_uint_theorems UInt8
declare_bitwise_uint_theorems UInt16
declare_bitwise_uint_theorems UInt32
declare_bitwise_uint_theorems UInt64
declare_bitwise_uint_theorems USize
