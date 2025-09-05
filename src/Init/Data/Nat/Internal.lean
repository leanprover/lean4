/-
Copyright (c) 2025 Robin Arnez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Robin Arnez
-/
module

prelude
public import Init.Data.UInt.Basic

public section

@[inline]
private unsafe def Nat.Internal.isScalarImpl (x : Nat) : Bool :=
  ptrAddrUnsafe x &&& 1 == 1

/--
Low-level function that returns whether the provided number is a "small natural number".

Small natural numbers are not allocated on the heap but instead have
their value encoded directly in their pointer address.
-/
@[implemented_by isScalarImpl, expose]
def Nat.Internal.isScalar (x : Nat) : Bool :=
  x < USize.size / 2

set_option linter.unusedVariables.funArgs false in
@[inline]
private unsafe def Nat.Internal.unboxImpl (x : Nat) (h : isScalar x) : USize :=
  ptrAddrUnsafe x >>> 1

/--
Low-level function that returns the `USize` value of a small natural number (see `isScalar`).
-/
@[implemented_by unboxImpl, expose]
def Nat.Internal.unbox (x : Nat) (h : isScalar x) : USize :=
  USize.ofNat x
