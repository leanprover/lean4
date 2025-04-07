/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.UInt.Basic

set_option linter.missingDocs true

/-!
This module contains the definition of signed fixed width integer types as well as basic arithmetic
and bitwise operations on top of it.
-/

/--
Signed 8-bit integers.

This type has special support in the compiler so it can be represented by an unboxed 8-bit value.
-/
structure Int8 where
  private ofUInt8 ::
  /--
  Converts an 8-bit signed integer into the 8-bit unsigned integer that is its two's complement
  encoding.
  -/
  toUInt8 : UInt8

/--
Signed 16-bit integers.

This type has special support in the compiler so it can be represented by an unboxed 16-bit value.
-/
structure Int16 where
  private ofUInt16 ::
  /--
  Converts an 16-bit signed integer into the 16-bit unsigned integer that is its two's complement
  encoding.
  -/
  toUInt16 : UInt16

/--
Signed 32-bit integers.

This type has special support in the compiler so it can be represented by an unboxed 32-bit value.
-/
structure Int32 where
  private ofUInt32 ::
  /--
  Converts an 32-bit signed integer into the 32-bit unsigned integer that is its two's complement
  encoding.
  -/
  toUInt32 : UInt32

/--
Signed 64-bit integers.

This type has special support in the compiler so it can be represented by an unboxed 64-bit value.
-/
structure Int64 where
  private ofUInt64 ::
  /--
  Converts an 64-bit signed integer into the 64-bit unsigned integer that is its two's complement
  encoding.
  -/
  toUInt64 : UInt64

/--
Signed integers that are the size of a word on the platform's architecture.

On a 32-bit architecture, `ISize` is equivalent to `Int32`. On a 64-bit machine, it is equivalent to
`Int64`. This type has special support in the compiler so it can be represented by an unboxed value.
-/
structure ISize where
  private ofUSize ::
  /--
  Converts a word-sized signed integer into the word-sized unsigned integer that is its two's
  complement encoding.
  -/
  toUSize : USize

/-- The number of distinct values representable by `Int8`, that is, `2^8 = 256`. -/
abbrev Int8.size : Nat := 256

/--
Obtain the `BitVec` that contains the 2's complement representation of the `Int8`.
-/
@[inline] def Int8.toBitVec (x : Int8) : BitVec 8 := x.toUInt8.toBitVec

theorem Int8.toBitVec.inj : {x y : Int8} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `Int8` that is 2's complement equivalent to the `UInt8`. -/
@[inline] def UInt8.toInt8 (i : UInt8) : Int8 := Int8.ofUInt8 i
@[inline, deprecated UInt8.toInt8 (since := "2025-02-13"), inherit_doc UInt8.toInt8]
def Int8.mk (i : UInt8) : Int8 := UInt8.toInt8 i
/--
Converts an arbitrary-precision integer to an 8-bit integer, wrapping on overflow or underflow.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int8.ofInt 48 = 48`
 * `Int8.ofInt (-115) = -115`
 * `Int8.ofInt (-129) = 127`
 * `Int8.ofInt (128) = -128`
-/
@[extern "lean_int8_of_int"]
def Int8.ofInt (i : @& Int) : Int8 := ⟨⟨BitVec.ofInt 8 i⟩⟩
/--
Converts a natural number to an 8-bit signed integer, wrapping around on overflow.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int8.ofNat 53 = 53`
 * `Int8.ofNat 127 = 127`
 * `Int8.ofNat 128 = -128`
 * `Int8.ofNat 255 = -1`
-/
@[extern "lean_int8_of_nat"]
def Int8.ofNat (n : @& Nat) : Int8 := ⟨⟨BitVec.ofNat 8 n⟩⟩
/--
Converts an arbitrary-precision integer to an 8-bit integer, wrapping on overflow or underflow.

Examples:
 * `Int.toInt8 48 = 48`
 * `Int.toInt8 (-115) = -115`
 * `Int.toInt8 (-129) = 127`
 * `Int.toInt8 (128) = -128`
-/
abbrev Int.toInt8 := Int8.ofInt
/--
Converts a natural number to an 8-bit signed integer, wrapping around to negative numbers on
overflow.

Examples:
 * `Nat.toInt8 53 = 53`
 * `Nat.toInt8 127 = 127`
 * `Nat.toInt8 128 = -128`
 * `Nat.toInt8 255 = -1`
-/
abbrev Nat.toInt8 := Int8.ofNat

/--
Converts an 8-bit signed integer to an arbitrary-precision integer that denotes the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_to_int"]
def Int8.toInt (i : Int8) : Int := i.toBitVec.toInt
/--
Converts an 8-bit signed integer to a natural number, mapping all negative numbers to `0`.

Use `Int8.toBitVec` to obtain the two's complement representation.
-/
@[inline] def Int8.toNatClampNeg (i : Int8) : Nat := i.toInt.toNat
@[inline, deprecated Int8.toNatClampNeg (since := "2025-02-13"), inherit_doc Int8.toNatClampNeg]
def Int8.toNat (i : Int8) : Nat := i.toInt.toNat
/-- Obtains the `Int8` whose 2's complement representation is the given `BitVec 8`. -/
@[inline] def Int8.ofBitVec (b : BitVec 8) : Int8 := ⟨⟨b⟩⟩
/--
Negates 8-bit signed integers. Usually accessed via the `-` prefix operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_neg"]
def Int8.neg (i : Int8) : Int8 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int8 where
  toString i := toString i.toInt
instance : Repr Int8 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom Int8 := ⟨⟩

instance : Hashable Int8 where
  hash i := i.toUInt8.toUInt64

instance Int8.instOfNat : OfNat Int8 n := ⟨Int8.ofNat n⟩
instance Int8.instNeg : Neg Int8 where
  neg := Int8.neg

/-- The largest number that `Int8` can represent: `2^7 - 1 = 127`. -/
abbrev Int8.maxValue : Int8 := 127
/-- The smallest number that `Int8` can represent: `-2^7 = -128`. -/
abbrev Int8.minValue : Int8 := -128
/-- Constructs an `Int8` from an `Int` that is known to be in bounds. -/
@[inline]
def Int8.ofIntLE (i : Int) (_hl : Int8.minValue.toInt ≤ i) (_hr : i ≤ Int8.maxValue.toInt) : Int8 :=
  Int8.ofInt i
/-- Constructs an `Int8` from an `Int`, clamping if the value is too small or too large. -/
def Int8.ofIntTruncate (i : Int) : Int8 :=
  if hl : Int8.minValue.toInt ≤ i then
    if hr : i ≤ Int8.maxValue.toInt then
      Int8.ofIntLE i hl hr
    else
      Int8.minValue
  else
    Int8.minValue
/--
Adds two 8-bit signed integers, wrapping around on over- or underflow. Usually accessed via the `+`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_add"]
protected def Int8.add (a b : Int8) : Int8 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
/--
Subtracts one 8-bit signed integer from another, wrapping around on over- or underflow. Usually
accessed via the `-` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_sub"]
protected def Int8.sub (a b : Int8) : Int8 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
/--
Multiplies two 8-bit signed integers, wrapping around on over- or underflow.  Usually accessed via
the `*` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_mul"]
protected def Int8.mul (a b : Int8) : Int8 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
/--
Truncating division for 8-bit signed integers, rounding towards zero. Usually accessed via the `/`
operator.

Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.

Examples:
* `Int8.div 10 3 = 3`
* `Int8.div 10 (-3) = (-3)`
* `Int8.div (-10) (-3) = 3`
* `Int8.div (-10) 3 = (-3)`
* `Int8.div 10 0 = 0`
-/
@[extern "lean_int8_div"]
protected def Int8.div (a b : Int8) : Int8 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
/--
The modulo operator for 8-bit signed integers, which computes the remainder when dividing one
integer by another with the T-rounding convention used by `Int8.div`. Usually accessed via the `%`
operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `Int8.mod 5 2 = 1`
* `Int8.mod 5 (-2) = 1`
* `Int8.mod (-5) 2 = (-1)`
* `Int8.mod (-5) (-2) = (-1)`
* `Int8.mod 4 2 = 0`
* `Int8.mod 4 (-2) = 0`
* `Int8.mod 4 0 = 4`
* `Int8.mod (-4) 0 = (-4)`
-/
@[extern "lean_int8_mod"]
protected def Int8.mod (a b : Int8) : Int8 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
/--
Bitwise and for 8-bit signed integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set,
according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_land"]
protected def Int8.land (a b : Int8) : Int8 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
/--
Bitwise or for 8-bit signed integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_lor"]
protected def Int8.lor (a b : Int8) : Int8 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
/--
Bitwise exclusive or for 8-bit signed integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_xor"]
protected def Int8.xor (a b : Int8) : Int8 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
/--
Bitwise left shift for 8-bit signed integers. Usually accessed via the `<<<` operator.

Signed integers are interpreted as bitvectors according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_shift_left"]
protected def Int8.shiftLeft (a b : Int8) : Int8 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 8)⟩⟩
/--
Arithmetic right shift for 8-bit signed integers. Usually accessed via the `<<<` operator.

The high bits are filled with the value of the most significant bit.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_shift_right"]
protected def Int8.shiftRight (a b : Int8) : Int8 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 8)⟩⟩
/--
Bitwise complement, also known as bitwise negation, for 8-bit signed integers. Usually accessed via
the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.
Integers use the two's complement representation, so `Int8.complement a = -(a + 1)`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_complement"]
protected def Int8.complement (a : Int8) : Int8 := ⟨⟨~~~a.toBitVec⟩⟩
/--
Computes the absolute value of an 8-bit signed integer.

This function is equivalent to `if a < 0 then -a else a`, so in particular `Int8.minValue` will be
mapped to `Int8.minValue`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_abs"]
protected def Int8.abs (a : Int8) : Int8 := ⟨⟨a.toBitVec.abs⟩⟩

/--
Decides whether two 8-bit signed integers are equal. Usually accessed via the `DecidableEq Int8`
instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int8.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : Int8) = 7 then "yes" else "no") = "no"`
 * `show (7 : Int8) = 7 by decide`
-/
@[extern "lean_int8_dec_eq"]
def Int8.decEq (a b : Int8) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int8.noConfusion h' (fun h' => absurd h' h))

/--
Strict inequality of 8-bit signed integers, defined as inequality of the corresponding integers.
Usually accessed via the `<` operator.
-/
protected def Int8.lt (a b : Int8) : Prop := a.toBitVec.slt b.toBitVec
/--
Non-strict inequality of 8-bit signed integers, defined as inequality of the corresponding integers.
Usually accessed via the `≤` operator.
-/
protected def Int8.le (a b : Int8) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int8 where
  default := 0

instance : Add Int8         := ⟨Int8.add⟩
instance : Sub Int8         := ⟨Int8.sub⟩
instance : Mul Int8         := ⟨Int8.mul⟩
instance : Mod Int8         := ⟨Int8.mod⟩
instance : Div Int8         := ⟨Int8.div⟩
instance : LT Int8          := ⟨Int8.lt⟩
instance : LE Int8          := ⟨Int8.le⟩
instance : Complement Int8  := ⟨Int8.complement⟩
instance : AndOp Int8       := ⟨Int8.land⟩
instance : OrOp Int8        := ⟨Int8.lor⟩
instance : Xor Int8         := ⟨Int8.xor⟩
instance : ShiftLeft Int8   := ⟨Int8.shiftLeft⟩
instance : ShiftRight Int8  := ⟨Int8.shiftRight⟩
instance : DecidableEq Int8 := Int8.decEq

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_int8"]
def Bool.toInt8 (b : Bool) : Int8 := if b then 1 else 0

/--
Decides whether one 8-bit signed integer is strictly less than another. Usually accessed via the
`DecidableLT Int8` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : Int8) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : Int8) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : Int8) < 7) by decide`
-/
@[extern "lean_int8_dec_lt"]
def Int8.decLt (a b : Int8) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

/--
Decides whether one 8-bit signed integer is less than or equal to another. Usually accessed via the
`DecidableLE Int8` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : Int8) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : Int8) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : Int8) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : Int8) ≤ 7 by decide`
-/
@[extern "lean_int8_dec_le"]
def Int8.decLe (a b : Int8) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : Int8) : Decidable (a < b) := Int8.decLt a b
instance (a b : Int8) : Decidable (a ≤ b) := Int8.decLe a b
instance : Max Int8 := maxOfLe
instance : Min Int8 := minOfLe

/-- The number of distinct values representable by `Int16`, that is, `2^16 = 65536`. -/
abbrev Int16.size : Nat := 65536

/--
Obtain the `BitVec` that contains the 2's complement representation of the `Int16`.
-/
@[inline] def Int16.toBitVec (x : Int16) : BitVec 16 := x.toUInt16.toBitVec

theorem Int16.toBitVec.inj : {x y : Int16} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `Int16` that is 2's complement equivalent to the `UInt16`. -/
@[inline] def UInt16.toInt16 (i : UInt16) : Int16 := Int16.ofUInt16 i
@[inline, deprecated UInt16.toInt16 (since := "2025-02-13"), inherit_doc UInt16.toInt16]
def Int16.mk (i : UInt16) : Int16 := UInt16.toInt16 i
/--
Converts an arbitrary-precision integer to a 16-bit signed integer, wrapping on overflow or underflow.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int16.ofInt 48 = 48`
 * `Int16.ofInt (-129) = -129`
 * `Int16.ofInt (128) = 128`
 * `Int16.ofInt 70000 = 4464`
 * `Int16.ofInt (-40000) = 25536`
-/
@[extern "lean_int16_of_int"]
def Int16.ofInt (i : @& Int) : Int16 := ⟨⟨BitVec.ofInt 16 i⟩⟩
/--
Converts a natural number to a 16-bit signed integer, wrapping around on overflow.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int16.ofNat 127 = 127`
 * `Int16.ofNat 32767 = 32767`
 * `Int16.ofNat 32768 = -32768`
 * `Int16.ofNat 32770 = -32766`
-/
@[extern "lean_int16_of_nat"]
def Int16.ofNat (n : @& Nat) : Int16 := ⟨⟨BitVec.ofNat 16 n⟩⟩
/--
Converts an arbitrary-precision integer to a 16-bit integer, wrapping on overflow or underflow.

Examples:
 * `Int.toInt16 48 = 48`
 * `Int.toInt16 (-129) = -129`
 * `Int.toInt16 (128) = 128`
 * `Int.toInt16 70000 = 4464`
 * `Int.toInt16 (-40000) = 25536`
-/
abbrev Int.toInt16 := Int16.ofInt
/--
Converts a natural number to a 16-bit signed integer, wrapping around to negative numbers on
overflow.

Examples:
 * `Nat.toInt16 127 = 127`
 * `Nat.toInt16 32767 = 32767`
 * `Nat.toInt16 32768 = -32768`
 * `Nat.toInt16 32770 = -32766`
-/
abbrev Nat.toInt16 := Int16.ofNat

/--
Converts a 16-bit signed integer to an arbitrary-precision integer that denotes the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_to_int"]
def Int16.toInt (i : Int16) : Int := i.toBitVec.toInt
/--
Converts a 16-bit signed integer to a natural number, mapping all negative numbers to `0`.

Use `Int16.toBitVec` to obtain the two's complement representation.
-/
@[inline] def Int16.toNatClampNeg (i : Int16) : Nat := i.toInt.toNat
@[inline, deprecated Int16.toNatClampNeg (since := "2025-02-13"), inherit_doc Int16.toNatClampNeg]
def Int16.toNat (i : Int16) : Nat := i.toInt.toNat
/-- Obtains the `Int16` whose 2's complement representation is the given `BitVec 16`. -/
@[inline] def Int16.ofBitVec (b : BitVec 16) : Int16 := ⟨⟨b⟩⟩
/--
Converts 16-bit signed integers to 8-bit signed integers by truncating their bitvector
representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_to_int8"]
def Int16.toInt8 (a : Int16) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
/--
Converts 8-bit signed integers to 16-bit signed integers that denote the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_to_int16"]
def Int8.toInt16 (a : Int8) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
/--
Negates 16-bit signed integers. Usually accessed via the `-` prefix operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_neg"]
def Int16.neg (i : Int16) : Int16 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int16 where
  toString i := toString i.toInt
instance : Repr Int16 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom Int16 := ⟨⟩

instance : Hashable Int16 where
  hash i := i.toUInt16.toUInt64

instance Int16.instOfNat : OfNat Int16 n := ⟨Int16.ofNat n⟩
instance Int16.instNeg : Neg Int16 where
  neg := Int16.neg

/-- The largest number that `Int16` can represent: `2^15 - 1 = 32767`. -/
abbrev Int16.maxValue : Int16 := 32767
/-- The smallest number that `Int16` can represent: `-2^15 = -32768`. -/
abbrev Int16.minValue : Int16 := -32768
/-- Constructs an `Int16` from an `Int` that is known to be in bounds. -/
@[inline]
def Int16.ofIntLE (i : Int) (_hl : Int16.minValue.toInt ≤ i) (_hr : i ≤ Int16.maxValue.toInt) : Int16 :=
  Int16.ofInt i
/-- Constructs an `Int16` from an `Int`, clamping if the value is too small or too large. -/
def Int16.ofIntTruncate (i : Int) : Int16 :=
  if hl : Int16.minValue.toInt ≤ i then
    if hr : i ≤ Int16.maxValue.toInt then
      Int16.ofIntLE i hl hr
    else
      Int16.minValue
  else
    Int16.minValue

/--
Adds two 16-bit signed integers, wrapping around on over- or underflow.  Usually accessed via the `+`
operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_add"]
protected def Int16.add (a b : Int16) : Int16 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
/--
Subtracts one 16-bit signed integer from another, wrapping around on over- or underflow. Usually
accessed via the `-` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_sub"]
protected def Int16.sub (a b : Int16) : Int16 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
/--
Multiplies two 16-bit signed integers, wrapping around on over- or underflow.  Usually accessed via
the `*` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_mul"]
protected def Int16.mul (a b : Int16) : Int16 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
/--
Truncating division for 16-bit signed integers, rounding towards zero. Usually accessed via the `/`
operator.

Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.

Examples:
* `Int16.div 10 3 = 3`
* `Int16.div 10 (-3) = (-3)`
* `Int16.div (-10) (-3) = 3`
* `Int16.div (-10) 3 = (-3)`
* `Int16.div 10 0 = 0`
-/
@[extern "lean_int16_div"]
protected def Int16.div (a b : Int16) : Int16 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
/--
The modulo operator for 16-bit signed integers, which computes the remainder when dividing one
integer by another with the T-rounding convention used by `Int16.div`. Usually accessed via the `%`
operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `Int16.mod 5 2 = 1`
* `Int16.mod 5 (-2) = 1`
* `Int16.mod (-5) 2 = (-1)`
* `Int16.mod (-5) (-2) = (-1)`
* `Int16.mod 4 2 = 0`
* `Int16.mod 4 (-2) = 0`
* `Int16.mod 4 0 = 4`
* `Int16.mod (-4) 0 = (-4)`
-/
@[extern "lean_int16_mod"]
protected def Int16.mod (a b : Int16) : Int16 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
/--
Bitwise and for 16-bit signed integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set,
according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_land"]
protected def Int16.land (a b : Int16) : Int16 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
/--
Bitwise or for 16-bit signed integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_lor"]
protected def Int16.lor (a b : Int16) : Int16 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
/--
Bitwise exclusive or for 16-bit signed integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_xor"]
protected def Int16.xor (a b : Int16) : Int16 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
/--
Bitwise left shift for 16-bit signed integers. Usually accessed via the `<<<` operator.

Signed integers are interpreted as bitvectors according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_shift_left"]
protected def Int16.shiftLeft (a b : Int16) : Int16 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 16)⟩⟩
/--
Arithmetic right shift for 16-bit signed integers. Usually accessed via the `<<<` operator.

The high bits are filled with the value of the most significant bit.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_shift_right"]
protected def Int16.shiftRight (a b : Int16) : Int16 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 16)⟩⟩
/--
Bitwise complement, also known as bitwise negation, for 16-bit signed integers. Usually accessed via
the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.
Integers use the two's complement representation, so `Int16.complement a = -(a + 1)`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_complement"]
protected def Int16.complement (a : Int16) : Int16 := ⟨⟨~~~a.toBitVec⟩⟩
/--
Computes the absolute value of a 16-bit signed integer.

This function is equivalent to `if a < 0 then -a else a`, so in particular `Int16.minValue` will be
mapped to `Int16.minValue`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_abs"]
protected def Int16.abs (a : Int16) : Int16 := ⟨⟨a.toBitVec.abs⟩⟩

/--
Decides whether two 16-bit signed integers are equal. Usually accessed via the `DecidableEq Int16`
instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int16.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : Int16) = 7 then "yes" else "no") = "no"`
 * `show (7 : Int16) = 7 by decide`
-/
@[extern "lean_int16_dec_eq"]
def Int16.decEq (a b : Int16) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int16.noConfusion h' (fun h' => absurd h' h))

/--
Strict inequality of 16-bit signed integers, defined as inequality of the corresponding integers.
Usually accessed via the `<` operator.
-/
protected def Int16.lt (a b : Int16) : Prop := a.toBitVec.slt b.toBitVec
/--
Non-strict inequality of 16-bit signed integers, defined as inequality of the corresponding
integers. Usually accessed via the `≤` operator.
-/
protected def Int16.le (a b : Int16) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int16 where
  default := 0

instance : Add Int16         := ⟨Int16.add⟩
instance : Sub Int16         := ⟨Int16.sub⟩
instance : Mul Int16         := ⟨Int16.mul⟩
instance : Mod Int16         := ⟨Int16.mod⟩
instance : Div Int16         := ⟨Int16.div⟩
instance : LT Int16          := ⟨Int16.lt⟩
instance : LE Int16          := ⟨Int16.le⟩
instance : Complement Int16  := ⟨Int16.complement⟩
instance : AndOp Int16       := ⟨Int16.land⟩
instance : OrOp Int16        := ⟨Int16.lor⟩
instance : Xor Int16         := ⟨Int16.xor⟩
instance : ShiftLeft Int16   := ⟨Int16.shiftLeft⟩
instance : ShiftRight Int16  := ⟨Int16.shiftRight⟩
instance : DecidableEq Int16 := Int16.decEq

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_int16"]
def Bool.toInt16 (b : Bool) : Int16 := if b then 1 else 0

/--
Decides whether one 16-bit signed integer is strictly less than another. Usually accessed via the
`DecidableLT Int16` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : Int16) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : Int16) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : Int16) < 7) by decide`
-/
@[extern "lean_int16_dec_lt"]
def Int16.decLt (a b : Int16) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

/--
Decides whether one 16-bit signed integer is less than or equal to another. Usually accessed via the
`DecidableLE Int16` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : Int16) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : Int16) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : Int16) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : Int16) ≤ 7 by decide`
-/
@[extern "lean_int16_dec_le"]
def Int16.decLe (a b : Int16) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : Int16) : Decidable (a < b) := Int16.decLt a b
instance (a b : Int16) : Decidable (a ≤ b) := Int16.decLe a b
instance : Max Int16 := maxOfLe
instance : Min Int16 := minOfLe

/-- The number of distinct values representable by `Int32`, that is, `2^32 = 4294967296`. -/
abbrev Int32.size : Nat := 4294967296

/--
Obtain the `BitVec` that contains the 2's complement representation of the `Int32`.
-/
@[inline] def Int32.toBitVec (x : Int32) : BitVec 32 := x.toUInt32.toBitVec

theorem Int32.toBitVec.inj : {x y : Int32} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `Int32` that is 2's complement equivalent to the `UInt32`. -/
@[inline] def UInt32.toInt32 (i : UInt32) : Int32 := Int32.ofUInt32 i
@[inline, deprecated UInt32.toInt32 (since := "2025-02-13"), inherit_doc UInt32.toInt32]
def Int32.mk (i : UInt32) : Int32 := UInt32.toInt32 i
/--
Converts an arbitrary-precision integer to a 32-bit integer, wrapping on overflow or underflow.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int32.ofInt 48 = 48`
 * `Int32.ofInt (-129) = -129`
 * `Int32.ofInt 70000 = 70000`
 * `Int32.ofInt (-40000) = -40000`
 * `Int32.ofInt 2147483648 = -2147483648`
 * `Int32.ofInt (-2147483649) = 2147483647`
-/
@[extern "lean_int32_of_int"]
def Int32.ofInt (i : @& Int) : Int32 := ⟨⟨BitVec.ofInt 32 i⟩⟩
/--
Converts a natural number to a 32-bit signed integer, wrapping around on overflow.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int32.ofNat 127 = 127`
 * `Int32.ofNat 32770 = 32770`
 * `Int32.ofNat 2_147_483_647 = 2_147_483_647`
 * `Int32.ofNat 2_147_483_648 = -2_147_483_648`
-/
@[extern "lean_int32_of_nat"]
def Int32.ofNat (n : @& Nat) : Int32 := ⟨⟨BitVec.ofNat 32 n⟩⟩
/--
Converts an arbitrary-precision integer to a 32-bit integer, wrapping on overflow or underflow.

Examples:
 * `Int.toInt32 48 = 48`
 * `Int.toInt32 (-129) = -129`
 * `Int.toInt32 70000 = 70000`
 * `Int.toInt32 (-40000) = -40000`
 * `Int.toInt32 2147483648 = -2147483648`
 * `Int.toInt32 (-2147483649) = 2147483647`
-/
abbrev Int.toInt32 := Int32.ofInt
/--
Converts a natural number to a 32-bit signed integer, wrapping around to negative numbers on
overflow.

Examples:
 * `Nat.toInt32 127 = 127`
 * `Nat.toInt32 32770 = 32770`
 * `Nat.toInt32 2_147_483_647 = 2_147_483_647`
 * `Nat.toInt32 2_147_483_648 = -2_147_483_648`
-/
abbrev Nat.toInt32 := Int32.ofNat
/--
Converts a 32-bit signed integer to an arbitrary-precision integer that denotes the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_to_int"]
def Int32.toInt (i : Int32) : Int := i.toBitVec.toInt
/--
Converts a 32-bit signed integer to a natural number, mapping all negative numbers to `0`.

Use `Int32.toBitVec` to obtain the two's complement representation.
-/
@[inline] def Int32.toNatClampNeg (i : Int32) : Nat := i.toInt.toNat
@[inline, deprecated Int32.toNatClampNeg (since := "2025-02-13"), inherit_doc Int32.toNatClampNeg]
def Int32.toNat (i : Int32) : Nat := i.toInt.toNat
/-- Obtains the `Int32` whose 2's complement representation is the given `BitVec 32`. -/
@[inline] def Int32.ofBitVec (b : BitVec 32) : Int32 := ⟨⟨b⟩⟩
/--
Converts a 32-bit signed integer to an 8-bit signed integer by truncating its bitvector
representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_to_int8"]
def Int32.toInt8 (a : Int32) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
/--
Converts a 32-bit signed integer to an 16-bit signed integer by truncating its bitvector
representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_to_int16"]
def Int32.toInt16 (a : Int32) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
/--
Converts 8-bit signed integers to 32-bit signed integers that denote the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_to_int32"]
def Int8.toInt32 (a : Int8) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
/--
Converts 8-bit signed integers to 32-bit signed integers that denote the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_to_int32"]
def Int16.toInt32 (a : Int16) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
/--
Negates 32-bit signed integers. Usually accessed via the `-` prefix operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_neg"]
def Int32.neg (i : Int32) : Int32 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int32 where
  toString i := toString i.toInt
instance : Repr Int32 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom Int32 := ⟨⟩

instance : Hashable Int32 where
  hash i := i.toUInt32.toUInt64

instance Int32.instOfNat : OfNat Int32 n := ⟨Int32.ofNat n⟩
instance Int32.instNeg : Neg Int32 where
  neg := Int32.neg

/-- The largest number that `Int32` can represent: `2^31 - 1 = 2147483647`. -/
abbrev Int32.maxValue : Int32 := 2147483647
/-- The smallest number that `Int32` can represent: `-2^31 = -2147483648`. -/
abbrev Int32.minValue : Int32 := -2147483648
/-- Constructs an `Int32` from an `Int` that is known to be in bounds. -/
@[inline]
def Int32.ofIntLE (i : Int) (_hl : Int32.minValue.toInt ≤ i) (_hr : i ≤ Int32.maxValue.toInt) : Int32 :=
  Int32.ofInt i
/-- Constructs an `Int32` from an `Int`, clamping if the value is too small or too large. -/
def Int32.ofIntTruncate (i : Int) : Int32 :=
  if hl : Int32.minValue.toInt ≤ i then
    if hr : i ≤ Int32.maxValue.toInt then
      Int32.ofIntLE i hl hr
    else
      Int32.minValue
  else
    Int32.minValue

/--
Adds two 32-bit signed integers, wrapping around on over- or underflow.  Usually accessed via the
`+` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_add"]
protected def Int32.add (a b : Int32) : Int32 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
/--
Subtracts one 32-bit signed integer from another, wrapping around on over- or underflow. Usually
accessed via the `-` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_sub"]
protected def Int32.sub (a b : Int32) : Int32 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
/--
Multiplies two 32-bit signed integers, wrapping around on over- or underflow.  Usually accessed via
the `*` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_mul"]
protected def Int32.mul (a b : Int32) : Int32 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
/--
Truncating division for 32-bit signed integers, rounding towards zero. Usually accessed via the `/`
operator.

Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.

Examples:
* `Int32.div 10 3 = 3`
* `Int32.div 10 (-3) = (-3)`
* `Int32.div (-10) (-3) = 3`
* `Int32.div (-10) 3 = (-3)`
* `Int32.div 10 0 = 0`
-/
@[extern "lean_int32_div"]
protected def Int32.div (a b : Int32) : Int32 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
/--
The modulo operator for 32-bit signed integers, which computes the remainder when dividing one
integer by another with the T-rounding convention used by `Int32.div`. Usually accessed via the `%`
operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `Int32.mod 5 2 = 1`
* `Int32.mod 5 (-2) = 1`
* `Int32.mod (-5) 2 = (-1)`
* `Int32.mod (-5) (-2) = (-1)`
* `Int32.mod 4 2 = 0`
* `Int32.mod 4 (-2) = 0`
* `Int32.mod 4 0 = 4`
* `Int32.mod (-4) 0 = (-4)`
-/
@[extern "lean_int32_mod"]
protected def Int32.mod (a b : Int32) : Int32 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
/--
Bitwise and for 32-bit signed integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set,
according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_land"]
protected def Int32.land (a b : Int32) : Int32 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
/--
Bitwise or for 32-bit signed integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_lor"]
protected def Int32.lor (a b : Int32) : Int32 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
/--
Bitwise exclusive or for 32-bit signed integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_xor"]
protected def Int32.xor (a b : Int32) : Int32 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
/--
Bitwise left shift for 32-bit signed integers. Usually accessed via the `<<<` operator.

Signed integers are interpreted as bitvectors according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_shift_left"]
protected def Int32.shiftLeft (a b : Int32) : Int32 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 32)⟩⟩
/--
Arithmetic right shift for 32-bit signed integers. Usually accessed via the `<<<` operator.

The high bits are filled with the value of the most significant bit.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_shift_right"]
protected def Int32.shiftRight (a b : Int32) : Int32 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 32)⟩⟩
/--
Bitwise complement, also known as bitwise negation, for 32-bit signed integers. Usually accessed via
the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.
Integers use the two's complement representation, so `Int32.complement a = -(a + 1)`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_complement"]
protected def Int32.complement (a : Int32) : Int32 := ⟨⟨~~~a.toBitVec⟩⟩
/--
Computes the absolute value of a 32-bit signed integer.

This function is equivalent to `if a < 0 then -a else a`, so in particular `Int32.minValue` will be
mapped to `Int32.minValue`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_abs"]
protected def Int32.abs (a : Int32) : Int32 := ⟨⟨a.toBitVec.abs⟩⟩

/--
Decides whether two 32-bit signed integers are equal. Usually accessed via the `DecidableEq Int32`
instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int32.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : Int32) = 7 then "yes" else "no") = "no"`
 * `show (7 : Int32) = 7 by decide`
-/
@[extern "lean_int32_dec_eq"]
def Int32.decEq (a b : Int32) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int32.noConfusion h' (fun h' => absurd h' h))

/--
Strict inequality of 32-bit signed integers, defined as inequality of the corresponding integers.
Usually accessed via the `<` operator.
-/
protected def Int32.lt (a b : Int32) : Prop := a.toBitVec.slt b.toBitVec
/--
Non-strict inequality of 32-bit signed integers, defined as inequality of the corresponding integers.
Usually accessed via the `≤` operator.
-/
protected def Int32.le (a b : Int32) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int32 where
  default := 0

instance : Add Int32         := ⟨Int32.add⟩
instance : Sub Int32         := ⟨Int32.sub⟩
instance : Mul Int32         := ⟨Int32.mul⟩
instance : Mod Int32         := ⟨Int32.mod⟩
instance : Div Int32         := ⟨Int32.div⟩
instance : LT Int32          := ⟨Int32.lt⟩
instance : LE Int32          := ⟨Int32.le⟩
instance : Complement Int32  := ⟨Int32.complement⟩
instance : AndOp Int32       := ⟨Int32.land⟩
instance : OrOp Int32        := ⟨Int32.lor⟩
instance : Xor Int32         := ⟨Int32.xor⟩
instance : ShiftLeft Int32   := ⟨Int32.shiftLeft⟩
instance : ShiftRight Int32  := ⟨Int32.shiftRight⟩
instance : DecidableEq Int32 := Int32.decEq

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_int32"]
def Bool.toInt32 (b : Bool) : Int32 := if b then 1 else 0

/--
Decides whether one 32-bit signed integer is strictly less than another. Usually accessed via the
`DecidableLT Int32` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : Int32) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : Int32) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : Int32) < 7) by decide`
-/
@[extern "lean_int32_dec_lt"]
def Int32.decLt (a b : Int32) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

/--
Decides whether one 32-bit signed integer is less than or equal to another. Usually accessed via the
`DecidableLE Int32` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : Int32) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : Int32) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : Int32) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : Int32) ≤ 7 by decide`
-/
@[extern "lean_int32_dec_le"]
def Int32.decLe (a b : Int32) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : Int32) : Decidable (a < b) := Int32.decLt a b
instance (a b : Int32) : Decidable (a ≤ b) := Int32.decLe a b
instance : Max Int32 := maxOfLe
instance : Min Int32 := minOfLe

/-- The number of distinct values representable by `Int64`, that is, `2^64 = 18446744073709551616`. -/
abbrev Int64.size : Nat := 18446744073709551616

/--
Obtain the `BitVec` that contains the 2's complement representation of the `Int64`.
-/
@[inline] def Int64.toBitVec (x : Int64) : BitVec 64 := x.toUInt64.toBitVec

theorem Int64.toBitVec.inj : {x y : Int64} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `Int64` that is 2's complement equivalent to the `UInt64`. -/
@[inline] def UInt64.toInt64 (i : UInt64) : Int64 := Int64.ofUInt64 i
@[inline, deprecated UInt64.toInt64 (since := "2025-02-13"), inherit_doc UInt64.toInt64]
def Int64.mk (i : UInt64) : Int64 := UInt64.toInt64 i
/--
Converts an arbitrary-precision integer to a 64-bit integer, wrapping on overflow or underflow.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int64.ofInt 48 = 48`
 * `Int64.ofInt (-40_000) = -40_000`
 * `Int64.ofInt 2_147_483_648 = 2_147_483_648`
 * `Int64.ofInt (-2_147_483_649) = -2_147_483_649`
 * `Int64.ofInt 9_223_372_036_854_775_808 = -9_223_372_036_854_775_808`
 * `Int64.ofInt (-9_223_372_036_854_775_809) = 9_223_372_036_854_775_807`
-/
@[extern "lean_int64_of_int"]
def Int64.ofInt (i : @& Int) : Int64 := ⟨⟨BitVec.ofInt 64 i⟩⟩
/--
Converts a natural number to a 64-bit signed integer, wrapping around to negative numbers on
overflow.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int64.ofNat 127 = 127`
 * `Int64.ofNat 2_147_483_648 = 2_147_483_648`
 * `Int64.ofNat 9_223_372_036_854_775_807 = 9_223_372_036_854_775_807`
 * `Int64.ofNat 9_223_372_036_854_775_808 = -9_223_372_036_854_775_808`
 * `Int64.ofNat 18_446_744_073_709_551_618 = 0`
-/
@[extern "lean_int64_of_nat"]
def Int64.ofNat (n : @& Nat) : Int64 := ⟨⟨BitVec.ofNat 64 n⟩⟩
/--
Converts an arbitrary-precision integer to a 64-bit integer, wrapping on overflow or underflow.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int.toInt64 48 = 48`
 * `Int.toInt64 (-40_000) = -40_000`
 * `Int.toInt64 2_147_483_648 = 2_147_483_648`
 * `Int.toInt64 (-2_147_483_649) = -2_147_483_649`
 * `Int.toInt64 9_223_372_036_854_775_808 = -9_223_372_036_854_775_808`
 * `Int.toInt64 (-9_223_372_036_854_775_809) = 9_223_372_036_854_775_807`
-/
abbrev Int.toInt64 := Int64.ofInt
/--
Converts a natural number to a 64-bit signed integer, wrapping around to negative numbers on
overflow.

Examples:
 * `Nat.toInt64 127 = 127`
 * `Nat.toInt64 2_147_483_648 = 2_147_483_648`
 * `Nat.toInt64 9_223_372_036_854_775_807 = 9_223_372_036_854_775_807`
 * `Nat.toInt64 9_223_372_036_854_775_808 = -9_223_372_036_854_775_808`
 * `Nat.toInt64 18_446_744_073_709_551_618 = 0`
-/
abbrev Nat.toInt64 := Int64.ofNat
/--
Converts a 64-bit signed integer to an arbitrary-precision integer that denotes the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_to_int_sint"]
def Int64.toInt (i : Int64) : Int := i.toBitVec.toInt
/--
Converts a 64-bit signed integer to a natural number, mapping all negative numbers to `0`.

Use `Int64.toBitVec` to obtain the two's complement representation.
-/
@[inline] def Int64.toNatClampNeg (i : Int64) : Nat := i.toInt.toNat
@[inline, deprecated Int64.toNatClampNeg (since := "2025-02-13"), inherit_doc Int64.toNatClampNeg]
def Int64.toNat (i : Int64) : Nat := i.toInt.toNat
/-- Obtains the `Int64` whose 2's complement representation is the given `BitVec 64`. -/
@[inline] def Int64.ofBitVec (b : BitVec 64) : Int64 := ⟨⟨b⟩⟩
/--
Converts a 64-bit signed integer to an 8-bit signed integer by truncating its bitvector
representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_to_int8"]
def Int64.toInt8 (a : Int64) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
/--
Converts a 64-bit signed integer to a 16-bit signed integer by truncating its bitvector
representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_to_int16"]
def Int64.toInt16 (a : Int64) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
/--
Converts a 64-bit signed integer to a 32-bit signed integer by truncating its bitvector
representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_to_int32"]
def Int64.toInt32 (a : Int64) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
/--
Converts 8-bit signed integers to 64-bit signed integers that denote the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_to_int64"]
def Int8.toInt64 (a : Int8) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
/--
Converts 16-bit signed integers to 64-bit signed integers that denote the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_to_int64"]
def Int16.toInt64 (a : Int16) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
/--
Converts 32-bit signed integers to 64-bit signed integers that denote the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_to_int64"]
def Int32.toInt64 (a : Int32) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
/--
Negates 64-bit signed integers. Usually accessed via the `-` prefix operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_neg"]
def Int64.neg (i : Int64) : Int64 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int64 where
  toString i := toString i.toInt
instance : Repr Int64 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom Int64 := ⟨⟩

instance : Hashable Int64 where
  hash i := i.toUInt64

instance Int64.instOfNat : OfNat Int64 n := ⟨Int64.ofNat n⟩
instance Int64.instNeg : Neg Int64 where
  neg := Int64.neg

/-- The largest number that `Int64` can represent: `2^63 - 1 = 9223372036854775807`. -/
abbrev Int64.maxValue : Int64 := 9223372036854775807
/-- The smallest number that `Int64` can represent: `-2^63 = -9223372036854775808`. -/
abbrev Int64.minValue : Int64 := -9223372036854775808
/-- Constructs an `Int64` from an `Int` that is known to be in bounds. -/
@[inline]
def Int64.ofIntLE (i : Int) (_hl : Int64.minValue.toInt ≤ i) (_hr : i ≤ Int64.maxValue.toInt) : Int64 :=
  Int64.ofInt i
/-- Constructs an `Int64` from an `Int`, clamping if the value is too small or too large. -/
def Int64.ofIntTruncate (i : Int) : Int64 :=
  if hl : Int64.minValue.toInt ≤ i then
    if hr : i ≤ Int64.maxValue.toInt then
      Int64.ofIntLE i hl hr
    else
      Int64.minValue
  else
    Int64.minValue

/--
Adds two 64-bit signed integers, wrapping around on over- or underflow.  Usually accessed via the
`+` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_add"]
protected def Int64.add (a b : Int64) : Int64 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
/--
Subtracts one 64-bit signed integer from another, wrapping around on over- or underflow. Usually
accessed via the `-` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_sub"]
protected def Int64.sub (a b : Int64) : Int64 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
/--
Multiplies two 64-bit signed integers, wrapping around on over- or underflow.  Usually accessed via
the `*` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_mul"]
protected def Int64.mul (a b : Int64) : Int64 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
/--
Truncating division for 64-bit signed integers, rounding towards zero. Usually accessed via the `/`
operator.

Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.

Examples:
* `Int64.div 10 3 = 3`
* `Int64.div 10 (-3) = (-3)`
* `Int64.div (-10) (-3) = 3`
* `Int64.div (-10) 3 = (-3)`
* `Int64.div 10 0 = 0`
-/
@[extern "lean_int64_div"]
protected def Int64.div (a b : Int64) : Int64 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
/--
The modulo operator for 64-bit signed integers, which computes the remainder when dividing one
integer by another with the T-rounding convention used by `Int64.div`. Usually accessed via the `%`
operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `Int64.mod 5 2 = 1`
* `Int64.mod 5 (-2) = 1`
* `Int64.mod (-5) 2 = (-1)`
* `Int64.mod (-5) (-2) = (-1)`
* `Int64.mod 4 2 = 0`
* `Int64.mod 4 (-2) = 0`
* `Int64.mod 4 0 = 4`
* `Int64.mod (-4) 0 = (-4)`
-/
@[extern "lean_int64_mod"]
protected def Int64.mod (a b : Int64) : Int64 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
/--
Bitwise and for 64-bit signed integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set,
according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_land"]
protected def Int64.land (a b : Int64) : Int64 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
/--
Bitwise or for 64-bit signed integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_lor"]
protected def Int64.lor (a b : Int64) : Int64 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
/--
Bitwise exclusive or for 64-bit signed integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_xor"]
protected def Int64.xor (a b : Int64) : Int64 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
/--
Bitwise left shift for 64-bit signed integers. Usually accessed via the `<<<` operator.

Signed integers are interpreted as bitvectors according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_shift_left"]
protected def Int64.shiftLeft (a b : Int64) : Int64 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 64)⟩⟩
/--
Arithmetic right shift for 64-bit signed integers. Usually accessed via the `<<<` operator.

The high bits are filled with the value of the most significant bit.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_shift_right"]
protected def Int64.shiftRight (a b : Int64) : Int64 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 64)⟩⟩
/--
Bitwise complement, also known as bitwise negation, for 64-bit signed integers. Usually accessed via
the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.
Integers use the two's complement representation, so `Int64.complement a = -(a + 1)`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_complement"]
protected def Int64.complement (a : Int64) : Int64 := ⟨⟨~~~a.toBitVec⟩⟩
/--
Computes the absolute value of a 64-bit signed integer.

This function is equivalent to `if a < 0 then -a else a`, so in particular `Int64.minValue` will be
mapped to `Int64.minValue`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_abs"]
protected def Int64.abs (a : Int64) : Int64 := ⟨⟨a.toBitVec.abs⟩⟩

/--
Decides whether two 64-bit signed integers are equal. Usually accessed via the `DecidableEq Int64`
instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `Int64.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : Int64) = 7 then "yes" else "no") = "no"`
 * `show (7 : Int64) = 7 by decide`
-/
@[extern "lean_int64_dec_eq"]
def Int64.decEq (a b : Int64) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int64.noConfusion h' (fun h' => absurd h' h))

/--
Strict inequality of 64-bit signed integers, defined as inequality of the corresponding integers.
Usually accessed via the `<` operator.
-/
protected def Int64.lt (a b : Int64) : Prop := a.toBitVec.slt b.toBitVec
/--
Non-strict inequality of 64-bit signed integers, defined as inequality of the corresponding integers.
Usually accessed via the `≤` operator.
-/
protected def Int64.le (a b : Int64) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int64 where
  default := 0

instance : Add Int64         := ⟨Int64.add⟩
instance : Sub Int64         := ⟨Int64.sub⟩
instance : Mul Int64         := ⟨Int64.mul⟩
instance : Mod Int64         := ⟨Int64.mod⟩
instance : Div Int64         := ⟨Int64.div⟩
instance : LT Int64          := ⟨Int64.lt⟩
instance : LE Int64          := ⟨Int64.le⟩
instance : Complement Int64  := ⟨Int64.complement⟩
instance : AndOp Int64       := ⟨Int64.land⟩
instance : OrOp Int64        := ⟨Int64.lor⟩
instance : Xor Int64         := ⟨Int64.xor⟩
instance : ShiftLeft Int64   := ⟨Int64.shiftLeft⟩
instance : ShiftRight Int64  := ⟨Int64.shiftRight⟩
instance : DecidableEq Int64 := Int64.decEq

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_int64"]
def Bool.toInt64 (b : Bool) : Int64 := if b then 1 else 0

/--
Decides whether one 8-bit signed integer is strictly less than another. Usually accessed via the
`DecidableLT Int64` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : Int64) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : Int64) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : Int64) < 7) by decide`
-/
@[extern "lean_int64_dec_lt"]
def Int64.decLt (a b : Int64) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))
/--
Decides whether one 8-bit signed integer is less than or equal to another. Usually accessed via the
`DecidableLE Int64` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : Int64) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : Int64) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : Int64) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : Int64) ≤ 7 by decide`
-/
@[extern "lean_int64_dec_le"]
def Int64.decLe (a b : Int64) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : Int64) : Decidable (a < b) := Int64.decLt a b
instance (a b : Int64) : Decidable (a ≤ b) := Int64.decLe a b
instance : Max Int64 := maxOfLe
instance : Min Int64 := minOfLe

/-- The number of distinct values representable by `ISize`, that is, `2^System.Platform.numBits`. -/
abbrev ISize.size : Nat := 2^System.Platform.numBits

/--
Obtain the `BitVec` that contains the 2's complement representation of the `ISize`.
-/
@[inline] def ISize.toBitVec (x : ISize) : BitVec System.Platform.numBits := x.toUSize.toBitVec

theorem ISize.toBitVec.inj : {x y : ISize} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `ISize` that is 2's complement equivalent to the `USize`. -/
@[inline] def USize.toISize (i : USize) : ISize := ISize.ofUSize i
@[inline, deprecated USize.toISize (since := "2025-02-13"), inherit_doc USize.toISize]
def ISize.mk (i : USize) : ISize := USize.toISize i
/--
Converts an arbitrary-precision integer to a word-sized signed integer, wrapping around on over- or
underflow.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_of_int"]
def ISize.ofInt (i : @& Int) : ISize := ⟨⟨BitVec.ofInt System.Platform.numBits i⟩⟩
/--
Converts an arbitrary-precision natural number to a word-sized signed integer, wrapping around on
overflow.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_of_nat"]
def ISize.ofNat (n : @& Nat) : ISize := ⟨⟨BitVec.ofNat System.Platform.numBits n⟩⟩
@[inherit_doc ISize.ofInt]
abbrev Int.toISize := ISize.ofInt
@[inherit_doc ISize.ofNat] abbrev Nat.toISize := ISize.ofNat
/--
Converts a word-sized signed integer to an arbitrary-precision integer that denotes the same number.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_to_int"]
def ISize.toInt (i : ISize) : Int := i.toBitVec.toInt
/--
Converts a word-sized signed integer to a natural number, mapping all negative numbers to `0`.

Use `ISize.toBitVec` to obtain the two's complement representation.
-/
@[inline] def ISize.toNatClampNeg (i : ISize) : Nat := i.toInt.toNat
@[inline, deprecated ISize.toNatClampNeg (since := "2025-02-13"), inherit_doc ISize.toNatClampNeg]
def ISize.toNat (i : ISize) : Nat := i.toInt.toNat
/-- Obtains the `ISize` whose 2's complement representation is the given `BitVec`. -/
@[inline] def ISize.ofBitVec (b : BitVec System.Platform.numBits) : ISize := ⟨⟨b⟩⟩
/--
Converts a word-sized signed integer to an 8-bit signed integer by truncating its bitvector representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_to_int8"]
def ISize.toInt8 (a : ISize) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
/--
Converts a word-sized integer to a 16-bit integer by truncating its bitvector representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_to_int16"]
def ISize.toInt16 (a : ISize) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
/--
Converts a word-sized signed integer to a 32-bit signed integer.

On 32-bit platforms, this conversion is lossless. On 64-bit platforms, the integer's bitvector
representation is truncated to 32 bits. This function is overridden at runtime with an efficient
implementation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_to_int32"]
def ISize.toInt32 (a : ISize) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
/--
Converts word-sized signed integers to 64-bit signed integers that denote the same number. This
conversion is lossless, because `ISize` is either `Int32` or `Int64`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_to_int64"]
def ISize.toInt64 (a : ISize) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
/--
Converts 8-bit signed integers to word-sized signed integers that denote the same number. This
conversion is lossless, because `ISize` is either `Int32` or `Int64`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int8_to_isize"]
def Int8.toISize (a : Int8) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
/--
Converts 16-bit signed integers to word-sized signed integers that denote the same number. This conversion is lossless, because
`ISize` is either `Int32` or `Int64`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int16_to_isize"]
def Int16.toISize (a : Int16) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
/--
Converts 32-bit signed integers to word-sized signed integers that denote the same number. This
conversion is lossless, because `ISize` is either `Int32` or `Int64`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int32_to_isize"]
def Int32.toISize (a : Int32) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
/--
Converts 64-bit signed integers to word-sized signed integers, truncating the bitvector
representation on 32-bit platforms. This conversion is lossless on 64-bit platforms.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_int64_to_isize"]
def Int64.toISize (a : Int64) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
/--
Negates word-sized signed integers. Usually accessed via the `-` prefix operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_neg"]
protected def ISize.neg (i : ISize) : ISize := ⟨⟨-i.toBitVec⟩⟩

instance : ToString ISize where
  toString i := toString i.toInt
instance : Repr ISize where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom ISize := ⟨⟩

instance : Hashable ISize where
  hash i := i.toUSize.toUInt64

instance ISize.instOfNat : OfNat ISize n := ⟨ISize.ofNat n⟩
instance ISize.instNeg : Neg ISize where
  neg := ISize.neg

/-- The largest number that `ISize` can represent: `2^(System.Platform.numBits - 1) - 1`. -/
abbrev ISize.maxValue : ISize := .ofInt (2 ^ (System.Platform.numBits - 1) - 1)
/-- The smallest number that `ISize` can represent: `-2^(System.Platform.numBits - 1)`. -/
abbrev ISize.minValue : ISize := .ofInt (-2 ^ (System.Platform.numBits - 1))

/-- Constructs an `ISize` from an `Int` that is known to be in bounds. -/
@[inline]
def ISize.ofIntLE (i : Int) (_hl : ISize.minValue.toInt ≤ i) (_hr : i ≤ ISize.maxValue.toInt) : ISize :=
  ISize.ofInt i
/-- Constructs an `ISize` from an `Int`, clamping if the value is too small or too large. -/
def ISize.ofIntTruncate (i : Int) : ISize :=
  if hl : ISize.minValue.toInt ≤ i then
    if hr : i ≤ ISize.maxValue.toInt then
      ISize.ofIntLE i hl hr
    else
      ISize.minValue
  else
    ISize.minValue

/--
Adds two word-sized signed integers, wrapping around on over- or underflow.  Usually accessed via
the `+` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_add"]
protected def ISize.add (a b : ISize) : ISize := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
/--
Subtracts one word-sized signed integer from another, wrapping around on over- or underflow. Usually
accessed via the `-` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_sub"]
protected def ISize.sub (a b : ISize) : ISize := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
/--
Multiplies two word-sized signed integers, wrapping around on over- or underflow.  Usually accessed
via the `*` operator.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_mul"]
protected def ISize.mul (a b : ISize) : ISize := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
/--
Truncating division for word-sized signed integers, rounding towards zero. Usually accessed via the
`/` operator.

Division by zero is defined to be zero.

This function is overridden at runtime with an efficient implementation.

Examples:
* `ISize.div 10 3 = 3`
* `ISize.div 10 (-3) = (-3)`
* `ISize.div (-10) (-3) = 3`
* `ISize.div (-10) 3 = (-3)`
* `ISize.div 10 0 = 0`
-/
@[extern "lean_isize_div"]
protected def ISize.div (a b : ISize) : ISize := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
/--
The modulo operator for word-sized signed integers, which computes the remainder when dividing one
integer by another with the T-rounding convention used by `ISize.div`. Usually accessed via the `%`
operator.

When the divisor is `0`, the result is the dividend rather than an error.

This function is overridden at runtime with an efficient implementation.

Examples:
* `ISize.mod 5 2 = 1`
* `ISize.mod 5 (-2) = 1`
* `ISize.mod (-5) 2 = (-1)`
* `ISize.mod (-5) (-2) = (-1)`
* `ISize.mod 4 2 = 0`
* `ISize.mod 4 (-2) = 0`
* `ISize.mod 4 0 = 4`
* `ISize.mod (-4) 0 = (-4)`
-/
@[extern "lean_isize_mod"]
protected def ISize.mod (a b : ISize) : ISize := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
/--
Bitwise and for word-sized signed integers. Usually accessed via the `&&&` operator.

Each bit of the resulting integer is set if the corresponding bits of both input integers are set,
according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_land"]
protected def ISize.land (a b : ISize) : ISize := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
/--
Bitwise or for word-sized signed integers. Usually accessed via the `|||` operator.

Each bit of the resulting integer is set if at least one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_lor"]
protected def ISize.lor (a b : ISize) : ISize := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
/--
Bitwise exclusive or for word-sized signed integers. Usually accessed via the `^^^` operator.

Each bit of the resulting integer is set if exactly one of the corresponding bits of the input
integers is set, according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_xor"]
protected def ISize.xor (a b : ISize) : ISize := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
/--
Bitwise left shift for word-sized signed integers. Usually accessed via the `<<<` operator.

Signed integers are interpreted as bitvectors according to the two's complement representation.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_shift_left"]
protected def ISize.shiftLeft (a b : ISize) : ISize := ⟨⟨a.toBitVec <<< (b.toBitVec.smod System.Platform.numBits)⟩⟩
/--
Arithmetic right shift for word-sized signed integers. Usually accessed via the `<<<` operator.

The high bits are filled with the value of
the most significant bit.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_shift_right"]
protected def ISize.shiftRight (a b : ISize) : ISize := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod System.Platform.numBits)⟩⟩
/--
Bitwise complement, also known as bitwise negation, for word-sized signed integers. Usually accessed
via the `~~~` prefix operator.

Each bit of the resulting integer is the opposite of the corresponding bit of the input integer.
Integers use the two's complement representation, so `ISize.complement a = -(a + 1)`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_complement"]
protected def ISize.complement (a : ISize) : ISize := ⟨⟨~~~a.toBitVec⟩⟩

/--
Computes the absolute value of a word-sized signed integer.

This function is equivalent to `if a < 0 then -a else a`, so in particular `ISize.minValue` will be
mapped to `ISize.minValue`.

This function is overridden at runtime with an efficient implementation.
-/
@[extern "lean_isize_abs"]
protected def ISize.abs (a : ISize) : ISize := ⟨⟨a.toBitVec.abs⟩⟩

/--
Decides whether two word-sized signed integers are equal. Usually accessed via the
`DecidableEq ISize` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `ISize.decEq 123 123 = .isTrue rfl`
 * `(if ((-7) : ISize) = 7 then "yes" else "no") = "no"`
 * `show (7 : ISize) = 7 by decide`
-/
@[extern "lean_isize_dec_eq"]
def ISize.decEq (a b : ISize) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => ISize.noConfusion h' (fun h' => absurd h' h))

/--
Strict inequality of word-sized signed integers, defined as inequality of the corresponding
integers. Usually accessed via the `<` operator.
-/
protected def ISize.lt (a b : ISize) : Prop := a.toBitVec.slt b.toBitVec
/--
Non-strict inequality of word-sized signed integers, defined as inequality of the corresponding
integers. Usually accessed via the `≤` operator.
-/
protected def ISize.le (a b : ISize) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited ISize where
  default := 0

instance : Add ISize         := ⟨ISize.add⟩
instance : Sub ISize         := ⟨ISize.sub⟩
instance : Mul ISize         := ⟨ISize.mul⟩
instance : Mod ISize         := ⟨ISize.mod⟩
instance : Div ISize         := ⟨ISize.div⟩
instance : LT ISize          := ⟨ISize.lt⟩
instance : LE ISize          := ⟨ISize.le⟩
instance : Complement ISize  := ⟨ISize.complement⟩
instance : AndOp ISize       := ⟨ISize.land⟩
instance : OrOp ISize        := ⟨ISize.lor⟩
instance : Xor ISize         := ⟨ISize.xor⟩
instance : ShiftLeft ISize   := ⟨ISize.shiftLeft⟩
instance : ShiftRight ISize  := ⟨ISize.shiftRight⟩
instance : DecidableEq ISize := ISize.decEq

/--
Converts `true` to `1` and `false` to `0`.
-/
@[extern "lean_bool_to_isize"]
def Bool.toISize (b : Bool) : ISize := if b then 1 else 0

/--
Decides whether one word-sized signed integer is strictly less than another. Usually accessed via the
`DecidableLT ISize` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : ISize) < 7 then "yes" else "no") = "yes"`
 * `(if (5 : ISize) < 5 then "yes" else "no") = "no"`
 * `show ¬((7 : ISize) < 7) by decide`
-/
@[extern "lean_isize_dec_lt"]
def ISize.decLt (a b : ISize) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

/--
Decides whether one word-sized signed integer is less than or equal to another. Usually accessed via
the `DecidableLE ISize` instance.

This function is overridden at runtime with an efficient implementation.

Examples:
 * `(if ((-7) : ISize) ≤ 7 then "yes" else "no") = "yes"`
 * `(if (15 : ISize) ≤ 15 then "yes" else "no") = "yes"`
 * `(if (15 : ISize) ≤ 5 then "yes" else "no") = "no"`
 * `show (7 : ISize) ≤ 7 by decide`
-/
@[extern "lean_isize_dec_le"]
def ISize.decLe (a b : ISize) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : ISize) : Decidable (a < b) := ISize.decLt a b
instance (a b : ISize) : Decidable (a ≤ b) := ISize.decLe a b
instance : Max ISize := maxOfLe
instance : Min ISize := minOfLe
