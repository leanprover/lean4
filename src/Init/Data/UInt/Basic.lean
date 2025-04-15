/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.UInt.BasicAux
import Init.Data.BitVec.Basic

set_option linter.missingDocs true

open Nat

/-- Converts a `Fin UInt8.size` into the corresponding `UInt8`. -/
@[inline] def UInt8.ofFin (a : Fin UInt8.size) : UInt8 := ⟨⟨a⟩⟩
@[deprecated UInt8.ofBitVec (since := "2025-02-12"), inherit_doc UInt8.ofBitVec]
def UInt8.mk (bitVec : BitVec 8) : UInt8 :=
  UInt8.ofBitVec bitVec
@[inline, deprecated UInt8.ofNatLT (since := "2025-02-13"), inherit_doc UInt8.ofNatLT]
def UInt8.ofNatCore (n : Nat) (h : n < UInt8.size) : UInt8 :=
  UInt8.ofNatLT n h

/-- Converts an `Int` to a `UInt8` by taking the (non-negative remainder of the division by `2 ^ 8`. -/
def UInt8.ofInt (x : Int) : UInt8 := ofNat (x % 2 ^ 8).toNat

/--
Adds two 8-bit unsigned integers, wrapping around on overflow. Usually accessed via the `+`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_add"]
protected def UInt8.add (a b : UInt8) : UInt8 := ⟨a.toBitVec + b.toBitVec⟩
/--
Subtracts one 8-bit unsigned integer from another, wrapping around on underflow. Usually accessed
via the `-` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_sub"]
protected def UInt8.sub (a b : UInt8) : UInt8 := ⟨a.toBitVec - b.toBitVec⟩
/--
Multiplies two 8-bit unsigned integers, wrapping around on overflow.  Usually accessed via the `*`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_mul"]
protected def UInt8.mul (a b : UInt8) : UInt8 := ⟨a.toBitVec * b.toBitVec⟩
/--
Unsigned division for 8-bit unsigned integers, discarding the remainder. Usually accessed
via the `/` operator.

This operation is sometimes called “floor division.” Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_div"]
protected def UInt8.div (a b : UInt8) : UInt8 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
/--
The power operation, raising an 8-bit unsigned integer to a natural number power,
wrapping around on overflow. Usually accessed via the `^` operator.

This function is currently *not* overridden at runtime with an efficient implementation,
and should be used with caution. See https://github.com/leanprover/lean4/issues/7887.
-/
protected def UInt8.pow (x : UInt8) (n : Nat) : UInt8 :=
  match n with
  | 0 => 1
  | n + 1 => UInt8.mul (UInt8.pow x n) x
/--
The modulo operator for 8-bit unsigned integers, which computes the remainder when dividing one
integer by another. Usually accessed via the `%` operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `UInt8.mod 5 2 = 1`
* `UInt8.mod 4 2 = 0`
* `UInt8.mod 4 0 = 4`
-/
@[extern "lean_uint8_mod"]
protected def UInt8.mod (a b : UInt8) : UInt8 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
set_option linter.missingDocs false in
@[deprecated UInt8.mod (since := "2024-09-23")]
protected def UInt8.modn (a : UInt8) (n : Nat) : UInt8 := ⟨Fin.modn a.toFin n⟩
/--
Bitwise and for 8-bit unsigned integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_land"]
protected def UInt8.land (a b : UInt8) : UInt8 := ⟨a.toBitVec &&& b.toBitVec⟩
/--
Bitwise or for 8-bit unsigned integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_lor"]
protected def UInt8.lor (a b : UInt8) : UInt8 := ⟨a.toBitVec ||| b.toBitVec⟩
/--
Bitwise exclusive or for 8-bit unsigned integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_xor"]
protected def UInt8.xor (a b : UInt8) : UInt8 := ⟨a.toBitVec ^^^ b.toBitVec⟩
/--
Bitwise left shift for 8-bit unsigned integers. Usually accessed via the `<<<` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_shift_left"]
protected def UInt8.shiftLeft (a b : UInt8) : UInt8 := ⟨a.toBitVec <<< (UInt8.mod b 8).toBitVec⟩
/--
Bitwise right shift for 8-bit unsigned integers. Usually accessed via the `>>>` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_shift_right"]
protected def UInt8.shiftRight (a b : UInt8) : UInt8 := ⟨a.toBitVec >>> (UInt8.mod b 8).toBitVec⟩
/--
Strict inequality of 8-bit unsigned integers, defined as inequality of the corresponding
natural numbers. Usually accessed via the `<` operator.
-/
protected def UInt8.lt (a b : UInt8) : Prop := a.toBitVec < b.toBitVec
/--
Non-strict inequality of 8-bit unsigned integers, defined as inequality of the corresponding
natural numbers. Usually accessed via the `≤` operator.
-/
protected def UInt8.le (a b : UInt8) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add UInt8       := ⟨UInt8.add⟩
instance : Sub UInt8       := ⟨UInt8.sub⟩
instance : Mul UInt8       := ⟨UInt8.mul⟩
instance : Pow UInt8 Nat   := ⟨UInt8.pow⟩
instance : Mod UInt8       := ⟨UInt8.mod⟩

set_option linter.deprecated false in
instance : HMod UInt8 Nat UInt8 := ⟨UInt8.modn⟩

instance : Div UInt8       := ⟨UInt8.div⟩
instance : LT UInt8        := ⟨UInt8.lt⟩
instance : LE UInt8        := ⟨UInt8.le⟩

/--
Bitwise complement, also known as bitwise negation, for 8-bit unsigned integers. Usually accessed
via the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_complement"]
protected def UInt8.complement (a : UInt8) : UInt8 := ⟨~~~a.toBitVec⟩
/--
Negation of 8-bit unsigned integers, computed modulo `UInt8.size`.

`UInt8.neg a` is equivalent to `255 - a + 1`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_neg"]
protected def UInt8.neg (a : UInt8) : UInt8 := ⟨-a.toBitVec⟩

instance : Complement UInt8 := ⟨UInt8.complement⟩
instance : Neg UInt8 := ⟨UInt8.neg⟩
instance : AndOp UInt8     := ⟨UInt8.land⟩
instance : OrOp UInt8      := ⟨UInt8.lor⟩
instance : Xor UInt8       := ⟨UInt8.xor⟩
instance : ShiftLeft UInt8  := ⟨UInt8.shiftLeft⟩
instance : ShiftRight UInt8 := ⟨UInt8.shiftRight⟩

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_uint8"]
def Bool.toUInt8 (b : Bool) : UInt8 := if b then 1 else 0

/--
Decides whether one 8-bit unsigned integer is strictly less than another. Usually accessed via the
`DecidableLT UInt8` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if (6 : UInt8) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : UInt8) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : UInt8) < 7) by decide`
-/
@[extern "lean_uint8_dec_lt"]
def UInt8.decLt (a b : UInt8) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

/--
Decides whether one 8-bit unsigned integer is less than or equal to another. Usually accessed via the
`DecidableLE UInt8` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if (15 : UInt8) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : UInt8) ≤ 5 then "yes" else "no") = "no"`
 * `(if (5 : UInt8) ≤ 15 then "yes" else "no") = "yes"`
 * `show (7 : UInt8) ≤ 7 by decide`
-/
@[extern "lean_uint8_dec_le"]
def UInt8.decLe (a b : UInt8) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

instance (a b : UInt8) : Decidable (a < b) := UInt8.decLt a b
instance (a b : UInt8) : Decidable (a ≤ b) := UInt8.decLe a b
instance : Max UInt8 := maxOfLe
instance : Min UInt8 := minOfLe

/-- Converts a `Fin UInt16.size` into the corresponding `UInt16`. -/
@[inline] def UInt16.ofFin (a : Fin UInt16.size) : UInt16 := ⟨⟨a⟩⟩
@[deprecated UInt16.ofBitVec (since := "2025-02-12"), inherit_doc UInt16.ofBitVec]
def UInt16.mk (bitVec : BitVec 16) : UInt16 :=
  UInt16.ofBitVec bitVec
@[inline, deprecated UInt16.ofNatLT (since := "2025-02-13"), inherit_doc UInt16.ofNatLT]
def UInt16.ofNatCore (n : Nat) (h : n < UInt16.size) : UInt16 :=
  UInt16.ofNatLT n h

/-- Converts an `Int` to a `UInt16` by taking the (non-negative remainder of the division by `2 ^ 16`. -/
def UInt16.ofInt (x : Int) : UInt16 := ofNat (x % 2 ^ 16).toNat

/--
Adds two 16-bit unsigned integers, wrapping around on overflow. Usually accessed via the `+`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_add"]
protected def UInt16.add (a b : UInt16) : UInt16 := ⟨a.toBitVec + b.toBitVec⟩
/--
Subtracts one 16-bit unsigned integer from another, wrapping around on underflow. Usually accessed
via the `-` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_sub"]
protected def UInt16.sub (a b : UInt16) : UInt16 := ⟨a.toBitVec - b.toBitVec⟩
/--
Multiplies two 16-bit unsigned integers, wrapping around on overflow.  Usually accessed via the `*`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_mul"]
protected def UInt16.mul (a b : UInt16) : UInt16 := ⟨a.toBitVec * b.toBitVec⟩
/--
Unsigned division for 16-bit unsigned integers, discarding the remainder. Usually accessed
via the `/` operator.

This operation is sometimes called “floor division.” Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_div"]
protected def UInt16.div (a b : UInt16) : UInt16 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
/--
The power operation, raising a 16-bit unsigned integer to a natural number power,
wrapping around on overflow. Usually accessed via the `^` operator.

This function is currently *not* overridden at runtime with an efficient implementation,
and should be used with caution. See https://github.com/leanprover/lean4/issues/7887.
-/
protected def UInt16.pow (x : UInt16) (n : Nat) : UInt16 :=
  match n with
  | 0 => 1
  | n + 1 => UInt16.mul (UInt16.pow x n) x
/--
The modulo operator for 16-bit unsigned integers, which computes the remainder when dividing one
integer by another. Usually accessed via the `%` operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `UInt16.mod 5 2 = 1`
* `UInt16.mod 4 2 = 0`
* `UInt16.mod 4 0 = 4`
-/
@[extern "lean_uint16_mod"]
protected def UInt16.mod (a b : UInt16) : UInt16 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
set_option linter.missingDocs false in
@[deprecated UInt16.mod (since := "2024-09-23")]
protected def UInt16.modn (a : UInt16) (n : Nat) : UInt16 := ⟨Fin.modn a.toFin n⟩
/--
Bitwise and for 16-bit unsigned integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_land"]
protected def UInt16.land (a b : UInt16) : UInt16 := ⟨a.toBitVec &&& b.toBitVec⟩
/--
Bitwise or for 16-bit unsigned integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_lor"]
protected def UInt16.lor (a b : UInt16) : UInt16 := ⟨a.toBitVec ||| b.toBitVec⟩
/--
Bitwise exclusive or for 16-bit unsigned integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_xor"]
protected def UInt16.xor (a b : UInt16) : UInt16 := ⟨a.toBitVec ^^^ b.toBitVec⟩
/--
Bitwise left shift for 16-bit unsigned integers. Usually accessed via the `<<<` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_shift_left"]
protected def UInt16.shiftLeft (a b : UInt16) : UInt16 := ⟨a.toBitVec <<< (UInt16.mod b 16).toBitVec⟩
/--
Bitwise right shift for 16-bit unsigned integers. Usually accessed via the `>>>` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_shift_right"]
protected def UInt16.shiftRight (a b : UInt16) : UInt16 := ⟨a.toBitVec >>> (UInt16.mod b 16).toBitVec⟩
/--
Strict inequality of 16-bit unsigned integers, defined as inequality of the corresponding
natural numbers. Usually accessed via the `<` operator.
-/
protected def UInt16.lt (a b : UInt16) : Prop := a.toBitVec < b.toBitVec
/--
Non-strict inequality of 16-bit unsigned integers, defined as inequality of the corresponding
natural numbers. Usually accessed via the `≤` operator.
-/
protected def UInt16.le (a b : UInt16) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add UInt16       := ⟨UInt16.add⟩
instance : Sub UInt16       := ⟨UInt16.sub⟩
instance : Mul UInt16       := ⟨UInt16.mul⟩
instance : Pow UInt16 Nat   := ⟨UInt16.pow⟩
instance : Mod UInt16       := ⟨UInt16.mod⟩

set_option linter.deprecated false in
instance : HMod UInt16 Nat UInt16 := ⟨UInt16.modn⟩

instance : Div UInt16       := ⟨UInt16.div⟩
instance : LT UInt16        := ⟨UInt16.lt⟩
instance : LE UInt16        := ⟨UInt16.le⟩

/--
Bitwise complement, also known as bitwise negation, for 16-bit unsigned integers. Usually accessed
via the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_complement"]
protected def UInt16.complement (a : UInt16) : UInt16 := ⟨~~~a.toBitVec⟩
/--
Negation of 16-bit unsigned integers, computed modulo `UInt16.size`.

`UInt16.neg a` is equivalent to `65_535 - a + 1`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_neg"]
protected def UInt16.neg (a : UInt16) : UInt16 := ⟨-a.toBitVec⟩

instance : Complement UInt16 := ⟨UInt16.complement⟩
instance : Neg UInt16 := ⟨UInt16.neg⟩
instance : AndOp UInt16     := ⟨UInt16.land⟩
instance : OrOp UInt16      := ⟨UInt16.lor⟩
instance : Xor UInt16       := ⟨UInt16.xor⟩
instance : ShiftLeft UInt16  := ⟨UInt16.shiftLeft⟩
instance : ShiftRight UInt16 := ⟨UInt16.shiftRight⟩

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_uint16"]
def Bool.toUInt16 (b : Bool) : UInt16 := if b then 1 else 0

set_option bootstrap.genMatcherCode false in
/--
Decides whether one 16-bit unsigned integer is strictly less than another. Usually accessed via the
`DecidableLT UInt16` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if (6 : UInt16) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : UInt16) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : UInt16) < 7) by decide`
-/
@[extern "lean_uint16_dec_lt"]
def UInt16.decLt (a b : UInt16) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

set_option bootstrap.genMatcherCode false in
/--
Decides whether one 16-bit unsigned integer is less than or equal to another. Usually accessed via the
`DecidableLE UInt16` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if (15 : UInt16) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : UInt16) ≤ 5 then "yes" else "no") = "no"`
 * `(if (5 : UInt16) ≤ 15 then "yes" else "no") = "yes"`
 * `show (7 : UInt16) ≤ 7 by decide`
-/
@[extern "lean_uint16_dec_le"]
def UInt16.decLe (a b : UInt16) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

instance (a b : UInt16) : Decidable (a < b) := UInt16.decLt a b
instance (a b : UInt16) : Decidable (a ≤ b) := UInt16.decLe a b
instance : Max UInt16 := maxOfLe
instance : Min UInt16 := minOfLe

/-- Converts a `Fin UInt32.size` into the corresponding `UInt32`. -/
@[inline] def UInt32.ofFin (a : Fin UInt32.size) : UInt32 := ⟨⟨a⟩⟩
@[deprecated UInt32.ofBitVec (since := "2025-02-12"), inherit_doc UInt32.ofBitVec]
def UInt32.mk (bitVec : BitVec 32) : UInt32 :=
  UInt32.ofBitVec bitVec
@[inline, deprecated UInt32.ofNatLT (since := "2025-02-13"), inherit_doc UInt32.ofNatLT]
def UInt32.ofNatCore (n : Nat) (h : n < UInt32.size) : UInt32 :=
  UInt32.ofNatLT n h

/-- Converts an `Int` to a `UInt32` by taking the (non-negative remainder of the division by `2 ^ 32`. -/
def UInt32.ofInt (x : Int) : UInt32 := ofNat (x % 2 ^ 32).toNat

/--
Adds two 32-bit unsigned integers, wrapping around on overflow. Usually accessed via the `+`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_add"]
protected def UInt32.add (a b : UInt32) : UInt32 := ⟨a.toBitVec + b.toBitVec⟩
/--
Subtracts one 32-bit unsigned integer from another, wrapping around on underflow. Usually accessed
via the `-` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_sub"]
protected def UInt32.sub (a b : UInt32) : UInt32 := ⟨a.toBitVec - b.toBitVec⟩
/--
Multiplies two 32-bit unsigned integers, wrapping around on overflow.  Usually accessed via the `*`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_mul"]
protected def UInt32.mul (a b : UInt32) : UInt32 := ⟨a.toBitVec * b.toBitVec⟩
/--
Unsigned division for 32-bit unsigned integers, discarding the remainder. Usually accessed
via the `/` operator.

This operation is sometimes called “floor division.” Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_div"]
protected def UInt32.div (a b : UInt32) : UInt32 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
/--
The power operation, raising a 32-bit unsigned integer to a natural number power,
wrapping around on overflow. Usually accessed via the `^` operator.

This function is currently *not* overridden at runtime with an efficient implementation,
and should be used with caution. See https://github.com/leanprover/lean4/issues/7887.
-/
protected def UInt32.pow (x : UInt32) (n : Nat) : UInt32 :=
  match n with
  | 0 => 1
  | n + 1 => UInt32.mul (UInt32.pow x n) x
/--
The modulo operator for 32-bit unsigned integers, which computes the remainder when dividing one
integer by another. Usually accessed via the `%` operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `UInt32.mod 5 2 = 1`
* `UInt32.mod 4 2 = 0`
* `UInt32.mod 4 0 = 4`
-/
@[extern "lean_uint32_mod"]
protected def UInt32.mod (a b : UInt32) : UInt32 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
set_option linter.missingDocs false in
@[deprecated UInt32.mod (since := "2024-09-23")]
protected def UInt32.modn (a : UInt32) (n : Nat) : UInt32 := ⟨Fin.modn a.toFin n⟩
/--
Bitwise and for 32-bit unsigned integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_land"]
protected def UInt32.land (a b : UInt32) : UInt32 := ⟨a.toBitVec &&& b.toBitVec⟩
/--
Bitwise or for 32-bit unsigned integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_lor"]
protected def UInt32.lor (a b : UInt32) : UInt32 := ⟨a.toBitVec ||| b.toBitVec⟩
/--
Bitwise exclusive or for 32-bit unsigned integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_xor"]
protected def UInt32.xor (a b : UInt32) : UInt32 := ⟨a.toBitVec ^^^ b.toBitVec⟩
/--
Bitwise left shift for 32-bit unsigned integers. Usually accessed via the `<<<` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_shift_left"]
protected def UInt32.shiftLeft (a b : UInt32) : UInt32 := ⟨a.toBitVec <<< (UInt32.mod b 32).toBitVec⟩
/--
Bitwise right shift for 32-bit unsigned integers. Usually accessed via the `>>>` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_shift_right"]
protected def UInt32.shiftRight (a b : UInt32) : UInt32 := ⟨a.toBitVec >>> (UInt32.mod b 32).toBitVec⟩
/--
Strict inequality of 32-bit unsigned integers, defined as inequality of the corresponding
natural numbers. Usually accessed via the `<` operator.
-/
protected def UInt32.lt (a b : UInt32) : Prop := a.toBitVec < b.toBitVec
/--
Non-strict inequality of 32-bit unsigned integers, defined as inequality of the corresponding
natural numbers. Usually accessed via the `≤` operator.
-/
protected def UInt32.le (a b : UInt32) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add UInt32       := ⟨UInt32.add⟩
instance : Sub UInt32       := ⟨UInt32.sub⟩
instance : Mul UInt32       := ⟨UInt32.mul⟩
instance : Pow UInt32 Nat   := ⟨UInt32.pow⟩
instance : Mod UInt32       := ⟨UInt32.mod⟩

set_option linter.deprecated false in
instance : HMod UInt32 Nat UInt32 := ⟨UInt32.modn⟩

instance : Div UInt32       := ⟨UInt32.div⟩
instance : LT UInt32        := ⟨UInt32.lt⟩
instance : LE UInt32        := ⟨UInt32.le⟩

/--
Bitwise complement, also known as bitwise negation, for 32-bit unsigned integers. Usually accessed
via the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_complement"]
protected def UInt32.complement (a : UInt32) : UInt32 := ⟨~~~a.toBitVec⟩
/--
Negation of 32-bit unsigned integers, computed modulo `UInt32.size`.

`UInt32.neg a` is equivalent to `429_4967_295 - a + 1`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_neg"]
protected def UInt32.neg (a : UInt32) : UInt32 := ⟨-a.toBitVec⟩

instance : Complement UInt32 := ⟨UInt32.complement⟩
instance : Neg UInt32 := ⟨UInt32.neg⟩
instance : AndOp UInt32     := ⟨UInt32.land⟩
instance : OrOp UInt32      := ⟨UInt32.lor⟩
instance : Xor UInt32       := ⟨UInt32.xor⟩
instance : ShiftLeft UInt32  := ⟨UInt32.shiftLeft⟩
instance : ShiftRight UInt32 := ⟨UInt32.shiftRight⟩

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_uint32"]
def Bool.toUInt32 (b : Bool) : UInt32 := if b then 1 else 0

/-- Converts a `Fin UInt64.size` into the corresponding `UInt64`. -/
@[inline] def UInt64.ofFin (a : Fin UInt64.size) : UInt64 := ⟨⟨a⟩⟩
@[deprecated UInt64.ofBitVec (since := "2025-02-12"), inherit_doc UInt64.ofBitVec]
def UInt64.mk (bitVec : BitVec 64) : UInt64 :=
  UInt64.ofBitVec bitVec
@[inline, deprecated UInt64.ofNatLT (since := "2025-02-13"), inherit_doc UInt64.ofNatLT]
def UInt64.ofNatCore (n : Nat) (h : n < UInt64.size) : UInt64 :=
  UInt64.ofNatLT n h

/-- Converts an `Int` to a `UInt64` by taking the (non-negative remainder of the division by `2 ^ 64`. -/
def UInt64.ofInt (x : Int) : UInt64 := ofNat (x % 2 ^ 64).toNat

/--
Adds two 64-bit unsigned integers, wrapping around on overflow. Usually accessed via the `+`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_add"]
protected def UInt64.add (a b : UInt64) : UInt64 := ⟨a.toBitVec + b.toBitVec⟩
/--
Subtracts one 64-bit unsigned integer from another, wrapping around on underflow. Usually accessed
via the `-` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_sub"]
protected def UInt64.sub (a b : UInt64) : UInt64 := ⟨a.toBitVec - b.toBitVec⟩
/--
Multiplies two 64-bit unsigned integers, wrapping around on overflow.  Usually accessed via the `*`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_mul"]
protected def UInt64.mul (a b : UInt64) : UInt64 := ⟨a.toBitVec * b.toBitVec⟩
/--
Unsigned division for 64-bit unsigned integers, discarding the remainder. Usually accessed
via the `/` operator.

This operation is sometimes called “floor division.” Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_div"]
protected def UInt64.div (a b : UInt64) : UInt64 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
/--
The power operation, raising a 64-bit unsigned integer to a natural number power,
wrapping around on overflow. Usually accessed via the `^` operator.

This function is currently *not* overridden at runtime with an efficient implementation,
and should be used with caution. See https://github.com/leanprover/lean4/issues/7887.
-/
protected def UInt64.pow (x : UInt64) (n : Nat) : UInt64 :=
  match n with
  | 0 => 1
  | n + 1 => UInt64.mul (UInt64.pow x n) x
/--
The modulo operator for 64-bit unsigned integers, which computes the remainder when dividing one
integer by another. Usually accessed via the `%` operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `UInt64.mod 5 2 = 1`
* `UInt64.mod 4 2 = 0`
* `UInt64.mod 4 0 = 4`
-/
@[extern "lean_uint64_mod"]
protected def UInt64.mod (a b : UInt64) : UInt64 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
set_option linter.missingDocs false in
@[deprecated UInt64.mod (since := "2024-09-23")]
protected def UInt64.modn (a : UInt64) (n : Nat) : UInt64 := ⟨Fin.modn a.toFin n⟩
/--
Bitwise and for 64-bit unsigned integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_land"]
protected def UInt64.land (a b : UInt64) : UInt64 := ⟨a.toBitVec &&& b.toBitVec⟩
/--
Bitwise or for 64-bit unsigned integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_lor"]
protected def UInt64.lor (a b : UInt64) : UInt64 := ⟨a.toBitVec ||| b.toBitVec⟩
/--
Bitwise exclusive or for 64-bit unsigned integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_xor"]
protected def UInt64.xor (a b : UInt64) : UInt64 := ⟨a.toBitVec ^^^ b.toBitVec⟩
/--
Bitwise left shift for 64-bit unsigned integers. Usually accessed via the `<<<` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_shift_left"]
protected def UInt64.shiftLeft (a b : UInt64) : UInt64 := ⟨a.toBitVec <<< (UInt64.mod b 64).toBitVec⟩
/--
Bitwise right shift for 64-bit unsigned integers. Usually accessed via the `>>>` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_shift_right"]
protected def UInt64.shiftRight (a b : UInt64) : UInt64 := ⟨a.toBitVec >>> (UInt64.mod b 64).toBitVec⟩
/--
Strict inequality of 64-bit unsigned integers, defined as inequality of the corresponding
natural numbers. Usually accessed via the `<` operator.
-/
protected def UInt64.lt (a b : UInt64) : Prop := a.toBitVec < b.toBitVec
/--
Non-strict inequality of 64-bit unsigned integers, defined as inequality of the corresponding
natural numbers. Usually accessed via the `≤` operator.
-/
protected def UInt64.le (a b : UInt64) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add UInt64       := ⟨UInt64.add⟩
instance : Sub UInt64       := ⟨UInt64.sub⟩
instance : Mul UInt64       := ⟨UInt64.mul⟩
instance : Pow UInt64 Nat   := ⟨UInt64.pow⟩
instance : Mod UInt64       := ⟨UInt64.mod⟩

set_option linter.deprecated false in
instance : HMod UInt64 Nat UInt64 := ⟨UInt64.modn⟩

instance : Div UInt64       := ⟨UInt64.div⟩
instance : LT UInt64        := ⟨UInt64.lt⟩
instance : LE UInt64        := ⟨UInt64.le⟩

/--
Bitwise complement, also known as bitwise negation, for 64-bit unsigned integers. Usually accessed
via the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_complement"]
protected def UInt64.complement (a : UInt64) : UInt64 := ⟨~~~a.toBitVec⟩
/--
Negation of 64-bit unsigned integers, computed modulo `UInt64.size`.

`UInt64.neg a` is equivalent to `18_446_744_073_709_551_615 - a + 1`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_neg"]
protected def UInt64.neg (a : UInt64) : UInt64 := ⟨-a.toBitVec⟩

instance : Complement UInt64 := ⟨UInt64.complement⟩
instance : Neg UInt64 := ⟨UInt64.neg⟩
instance : AndOp UInt64     := ⟨UInt64.land⟩
instance : OrOp UInt64      := ⟨UInt64.lor⟩
instance : Xor UInt64       := ⟨UInt64.xor⟩
instance : ShiftLeft UInt64  := ⟨UInt64.shiftLeft⟩
instance : ShiftRight UInt64 := ⟨UInt64.shiftRight⟩

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_uint64"]
def Bool.toUInt64 (b : Bool) : UInt64 := if b then 1 else 0

/--
Decides whether one 64-bit unsigned integer is strictly less than another. Usually accessed via the
`DecidableLT UInt64` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if (6 : UInt64) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : UInt64) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : UInt64) < 7) by decide`
-/
@[extern "lean_uint64_dec_lt"]
def UInt64.decLt (a b : UInt64) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

/--
Decides whether one 64-bit unsigned integer is less than or equal to another. Usually accessed via the
`DecidableLE UInt64` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if (15 : UInt64) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : UInt64) ≤ 5 then "yes" else "no") = "no"`
 * `(if (5 : UInt64) ≤ 15 then "yes" else "no") = "yes"`
 * `show (7 : UInt64) ≤ 7 by decide`
-/
@[extern "lean_uint64_dec_le"]
def UInt64.decLe (a b : UInt64) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

instance (a b : UInt64) : Decidable (a < b) := UInt64.decLt a b
instance (a b : UInt64) : Decidable (a ≤ b) := UInt64.decLe a b
instance : Max UInt64 := maxOfLe
instance : Min UInt64 := minOfLe

/-- Converts a `Fin USize.size` into the corresponding `USize`. -/
@[inline] def USize.ofFin (a : Fin USize.size) : USize := ⟨⟨a⟩⟩
@[deprecated USize.ofBitVec (since := "2025-02-12"), inherit_doc USize.ofBitVec]
def USize.mk (bitVec : BitVec System.Platform.numBits) : USize :=
  USize.ofBitVec bitVec
@[inline, deprecated USize.ofNatLT (since := "2025-02-13"), inherit_doc USize.ofNatLT]
def USize.ofNatCore (n : Nat) (h : n < USize.size) : USize :=
  USize.ofNatLT n h

/-- Converts an `Int` to a `USize` by taking the (non-negative remainder of the division by `2 ^ numBits`. -/
def USize.ofInt (x : Int) : USize := ofNat (x % 2 ^ System.Platform.numBits).toNat

@[simp] theorem USize.le_size : 2 ^ 32 ≤ USize.size := by cases USize.size_eq <;> simp_all
@[simp] theorem USize.size_le : USize.size ≤ 2 ^ 64 := by cases USize.size_eq <;> simp_all

@[deprecated USize.size_le (since := "2025-02-24")]
theorem usize_size_le : USize.size ≤ 18446744073709551616 :=
  USize.size_le

@[deprecated USize.le_size (since := "2025-02-24")]
theorem le_usize_size : 4294967296 ≤ USize.size :=
  USize.le_size

/--
Multiplies two word-sized unsigned integers, wrapping around on overflow.  Usually accessed via the
`*` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_mul"]
protected def USize.mul (a b : USize) : USize := ⟨a.toBitVec * b.toBitVec⟩
/--
Unsigned division for word-sized unsigned integers, discarding the remainder. Usually accessed
via the `/` operator.

This operation is sometimes called “floor division.” Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_div"]
protected def USize.div (a b : USize) : USize := ⟨a.toBitVec / b.toBitVec⟩
/--
The power operation, raising a word-sized unsigned integer to a natural number power,
wrapping around on overflow. Usually accessed via the `^` operator.

This function is currently *not* overridden at runtime with an efficient implementation,
and should be used with caution. See https://github.com/leanprover/lean4/issues/7887.
-/
protected def USize.pow (x : USize) (n : Nat) : USize :=
  match n with
  | 0 => 1
  | n + 1 => USize.mul (USize.pow x n) x
/--
The modulo operator for word-sized unsigned integers, which computes the remainder when dividing one
integer by another. Usually accessed via the `%` operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `USize.mod 5 2 = 1`
* `USize.mod 4 2 = 0`
* `USize.mod 4 0 = 4`
-/
@[extern "lean_usize_mod"]
protected def USize.mod (a b : USize) : USize := ⟨a.toBitVec % b.toBitVec⟩
set_option linter.missingDocs false in
@[deprecated USize.mod (since := "2024-09-23")]
protected def USize.modn (a : USize) (n : Nat) : USize := ⟨Fin.modn a.toFin n⟩
/--
Bitwise and for word-sized unsigned integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_land"]
protected def USize.land (a b : USize) : USize := ⟨a.toBitVec &&& b.toBitVec⟩
/--
Bitwise or for word-sized unsigned integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_lor"]
protected def USize.lor (a b : USize) : USize := ⟨a.toBitVec ||| b.toBitVec⟩
/--
Bitwise exclusive or for word-sized unsigned integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of both input
integers are set.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_xor"]
protected def USize.xor (a b : USize) : USize := ⟨a.toBitVec ^^^ b.toBitVec⟩
/--
Bitwise left shift for word-sized unsigned integers. Usually accessed via the `<<<` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_shift_left"]
protected def USize.shiftLeft (a b : USize) : USize := ⟨a.toBitVec <<< (USize.mod b (USize.ofNat System.Platform.numBits)).toBitVec⟩
/--
Bitwise right shift for word-sized unsigned integers. Usually accessed via the `>>>` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_shift_right"]
protected def USize.shiftRight (a b : USize) : USize := ⟨a.toBitVec >>> (USize.mod b (USize.ofNat System.Platform.numBits)).toBitVec⟩
/--
Converts a natural number to a `USize`. Overflow is impossible on any supported platform because
`USize.size` is either `2^32` or `2^64`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_of_nat"]
def USize.ofNat32 (n : @& Nat) (h : n < 4294967296) : USize :=
  USize.ofNatLT n (Nat.lt_of_lt_of_le h USize.le_size)
/--
Converts 8-bit unsigned integers to word-sized unsigned integers.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint8_to_usize"]
def UInt8.toUSize (a : UInt8) : USize :=
  USize.ofNat32 a.toBitVec.toNat (Nat.lt_trans a.toBitVec.isLt (by decide))
/--
Converts word-sized unsigned integers to 8-bit unsigned integers. Wraps around on overflow.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_to_uint8"]
def USize.toUInt8 (a : USize) : UInt8 := a.toNat.toUInt8
/--
Converts 16-bit unsigned integers to word-sized unsigned integers.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint16_to_usize"]
def UInt16.toUSize (a : UInt16) : USize :=
  USize.ofNat32 a.toBitVec.toNat (Nat.lt_trans a.toBitVec.isLt (by decide))
/--
Converts word-sized unsigned integers to 16-bit unsigned integers. Wraps around on overflow.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_to_uint16"]
def USize.toUInt16 (a : USize) : UInt16 := a.toNat.toUInt16
/--
Converts 32-bit unsigned integers to word-sized unsigned integers.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint32_to_usize"]
def UInt32.toUSize (a : UInt32) : USize := USize.ofNat32 a.toBitVec.toNat a.toBitVec.isLt
/--
Converts word-sized unsigned integers to 32-bit unsigned integers. Wraps around on overflow, which
might occur on 64-bit architectures.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_to_uint32"]
def USize.toUInt32 (a : USize) : UInt32 := a.toNat.toUInt32
/--
Converts 64-bit unsigned integers to word-sized unsigned integers. On 32-bit machines, this may
overflow, which results in the value wrapping around (that is, it is reduced modulo `USize.size`).

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_uint64_to_usize"]
def UInt64.toUSize (a : UInt64) : USize := a.toNat.toUSize
/--
Converts word-sized unsigned integers to 32-bit unsigned integers. This cannot overflow because
`USize.size` is either `2^32` or `2^64`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_to_uint64"]
def USize.toUInt64 (a : USize) : UInt64 :=
  UInt64.ofNatLT a.toBitVec.toNat (Nat.lt_of_lt_of_le a.toBitVec.isLt USize.size_le)

instance : Mul USize       := ⟨USize.mul⟩
instance : Pow USize Nat   := ⟨USize.pow⟩
instance : Mod USize       := ⟨USize.mod⟩

set_option linter.deprecated false in
instance : HMod USize Nat USize := ⟨USize.modn⟩

instance : Div USize       := ⟨USize.div⟩

/--
Bitwise complement, also known as bitwise negation, for word-sized unsigned integers. Usually
accessed via the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_complement"]
protected def USize.complement (a : USize) : USize := ⟨~~~a.toBitVec⟩
/--
Negation of word-sized unsigned integers, computed modulo `USize.size`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_usize_neg"]
protected def USize.neg (a : USize) : USize := ⟨-a.toBitVec⟩

instance : Complement USize := ⟨USize.complement⟩
instance : Neg USize := ⟨USize.neg⟩
instance : AndOp USize      := ⟨USize.land⟩
instance : OrOp USize       := ⟨USize.lor⟩
instance : Xor USize        := ⟨USize.xor⟩
instance : ShiftLeft USize  := ⟨USize.shiftLeft⟩
instance : ShiftRight USize := ⟨USize.shiftRight⟩

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_usize"]
def Bool.toUSize (b : Bool) : USize := if b then 1 else 0

instance : Max USize := maxOfLe
instance : Min USize := minOfLe
