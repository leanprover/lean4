/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Float.Model.Format.Valid
public import Init.Data.Float.Model.Unpacked.Pack.Lemmas
public import Init.Data.Float.Model.Unpacked.Operations
public import Init.Data.Order.Factories

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

/--
The logical model for the `Float` type.

This is defined as the type of `UInt64` with the additional restriction that bit patterns encoding
a `NaN` must be exactly a chosen canonical `NaN`.

Most functions on `Float.Model` work by unpacking the `Float.Model` into the inductive type
`UnpackedFloat`, performing the operation there, and then repacking the result into a `Float.Model`.

It is not a goal of this development to serve as the basis for a general-purpose floating-point
library or to have any direct lemmas written about it at all. Rather, users interested in a library
about floating-point numbers should develop such a library completely separately, and users
interested in proving properties of their programs involving `Float` should prove that the
operations defined here are equivalent to the operations defined in the separate library and then
transfer lemmas from the library to the `Float` and `Float32` types.
-/
structure Float.Model where
  /-- The underlying bit pattern of the `Float.Model`. -/
  toBits : UInt64
  /-- The underlying bit pattern is valid according to the IEEE `binary64` format. -/
  valid : Float.Model.Format.binary64.Valid toBits.toBitVec

namespace Float.Model

/-- Unpack a `Float.Model` into the corresponding `UnpackedFloat`. -/
def unpack (f : Float.Model) : UnpackedFloat :=
  UnpackedFloat.unpack Format.binary64 f.toBits.toBitVec

/--
Pack an `UnpackedFloat` into the corresponding `Float.Model`.
This operation only gives a meaningful result if the float is
already correctly rounded for the `Format.binary64` format.
-/
def pack (f : UnpackedFloat) : Float.Model where
  toBits := UInt64.ofBitVec (UnpackedFloat.pack Format.binary64 f)
  valid := by simp

/--
Compute the sum of two `Float.Model`.
-/
def add (a b : Float.Model) : Float.Model :=
  pack (UnpackedFloat.add Format.binary64 a.unpack b.unpack)

/--
Compute the difference of two `Float.Model`.
-/
def sub (a b : Float.Model) : Float.Model :=
  pack (UnpackedFloat.sub Format.binary64 a.unpack b.unpack)

/--
Compute the product of two `Float.Model`.
-/
def mul (a b : Float.Model) : Float.Model :=
  pack (UnpackedFloat.mul Format.binary64 a.unpack b.unpack)

/--
Compute the quotient of two `Float.Model`.
-/
def div (a b : Float.Model) : Float.Model :=
  pack (UnpackedFloat.div Format.binary64 a.unpack b.unpack)

instance : Add Float.Model where
  add a b := a.add b

instance : Sub Float.Model where
  sub a b := a.sub b

instance : Mul Float.Model where
  mul a b := a.mul b

instance : Div Float.Model where
  div a b := a.div b

/--
Compute the square root of a `Float.Model`.
-/
def sqrt (a : Float.Model) : Float.Model :=
  pack (UnpackedFloat.sqrt Format.binary64 a.unpack)

/--
Negate a `Float.Model`.
-/
def neg (a : Float.Model) : Float.Model :=
  pack a.unpack.neg

instance : Neg Float.Model where
  neg a := a.neg

/--
Return a `Float.Model` with positive sign.
-/
def abs (a : Float.Model) : Float.Model :=
  pack a.unpack.abs

/--
Compute the ordering between two `Float.Model` as specified by IEEE. Returns an
`Option Ordering` to account for the fact that `NaN` is incomparable with everything.
Also, positive and negative zero are equal.
-/
protected def compare (a b : Float.Model) : Option Ordering :=
  a.unpack.compare b.unpack

/--
Determine whether `a` is less than or equal to `b` according to IEEE rules.

This is not a total ordering, and `≤` is not reflexive.
-/
protected def le (a b : Float.Model) : Bool :=
  a.unpack.le b.unpack

/--
Determine whether `a` is less than `b` according to IEEE rules.

This is not a total ordering.
-/
protected def lt (a b : Float.Model) : Bool :=
  a.unpack.lt b.unpack

/--
Determine whether `a` is equal to `b` according to IEEE rules.

This is not a reflexive relation.
-/
protected def beq (a b : Float.Model) : Bool :=
  a.unpack.beq b.unpack

instance : LE Float.Model where
  le a b := a.le b

instance : DecidableLE Float.Model :=
  inferInstanceAs (∀ (a b : Float.Model), Decidable (a.le b))

instance : LT Float.Model where
  lt a b := a.lt b

instance : DecidableLT Float.Model :=
  inferInstanceAs (∀ (a b : Float.Model), Decidable (a.lt b))

instance : BEq Float.Model where
  beq a b := a.beq b

instance : Min Float.Model :=
  Min.leftLeaningOfLE _

instance : Max Float.Model :=
  Max.leftLeaningOfLE _

/--
Returns `true` if the float represents a real number, i.e., it is neither infinite nor `NaN`.
-/
def isFinite (a : Float.Model) : Bool :=
  a.unpack.isFinite

/--
Returns `true` if the float is positive or negative infinity.
-/
def isInf (a : Float.Model) : Bool :=
  a.unpack.isInf

/--
Returns `true` if the float is `NaN`.
-/
def isNaN (a : Float.Model) : Bool :=
  a.unpack.isNaN

/--
Construct a `Float.Model` from its bit representation. This operation canonicalizes
all `NaN` inputs into the canonical `NaN`.
-/
def ofBits (a : UInt64) : Float.Model :=
  pack (UnpackedFloat.unpack Format.binary64 a.toBitVec)

/-- Converts an `Int` to a `Float.Model`, returning positive zero on zero. -/
def ofInt (n : Int) : Float.Model :=
  pack (UnpackedFloat.ofInt Format.binary64 n)

/-- Converts a `Nat` to a `Float.Model`, returning positive zero on zero. -/
def ofNat (n : Nat) : Float.Model :=
  pack (UnpackedFloat.ofNat Format.binary64 n)

/-- Converts a `UInt8` to a `Float.Model`, returning positive zero on zero. -/
def ofUInt8 (n : UInt8) : Float.Model :=
  pack (UnpackedFloat.ofUInt8 Format.binary64 n)

/-- Converts a `UInt16` to a `Float.Model`, returning positive zero on zero. -/
def ofUInt16 (n : UInt16) : Float.Model :=
  pack (UnpackedFloat.ofUInt16 Format.binary64 n)

/-- Converts a `UInt32` to a `Float.Model`, returning positive zero on zero. -/
def ofUInt32 (n : UInt32) : Float.Model :=
  pack (UnpackedFloat.ofUInt32 Format.binary64 n)

/-- Converts a `UInt64` to a `Float.Model`, returning positive zero on zero. -/
def ofUInt64 (n : UInt64) : Float.Model :=
  pack (UnpackedFloat.ofUInt64 Format.binary64 n)

/-- Converts a `USize` to a `Float.Model`, returning positive zero on zero. -/
def ofUSize (n : USize) : Float.Model :=
  pack (UnpackedFloat.ofUSize Format.binary64 n)

/-- Converts an `Int8` to a `Float.Model`, returning positive zero on zero. -/
def ofInt8 (n : Int8) : Float.Model :=
  pack (UnpackedFloat.ofInt8 Format.binary64 n)

/-- Converts an `Int16` to a `Float.Model`, returning positive zero on zero. -/
def ofInt16 (n : Int16) : Float.Model :=
  pack (UnpackedFloat.ofInt16 Format.binary64 n)

/-- Converts an `Int32` to a `Float.Model`, returning positive zero on zero. -/
def ofInt32 (n : Int32) : Float.Model :=
  pack (UnpackedFloat.ofInt32 Format.binary64 n)

/-- Converts an `Int64` to a `Float.Model`, returning positive zero on zero. -/
def ofInt64 (n : Int64) : Float.Model :=
  pack (UnpackedFloat.ofInt64 Format.binary64 n)

/-- Converts an `ISize` to a `Float.Model`, returning positive zero on zero. -/
def ofISize (n : ISize) : Float.Model :=
  pack (UnpackedFloat.ofISize Format.binary64 n)

/--
Converts a `Float.Model` to a `UInt8`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toUInt8 (f : Float.Model) : UInt8 := f.unpack.toUInt8

/--
Converts a `Float.Model` to a `UInt16`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toUInt16 (f : Float.Model) : UInt16 := f.unpack.toUInt16

/--
Converts a `Float.Model` to a `UInt32`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toUInt32 (f : Float.Model) : UInt32 := f.unpack.toUInt32

/--
Converts a `Float.Model` to a `UInt64`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toUInt64 (f : Float.Model) : UInt64 := f.unpack.toUInt64

/--
Converts a `Float.Model` to a `USize`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toUSize (f : Float.Model) : USize := f.unpack.toUSize

/--
Converts a `Float.Model` to an `Int8`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toInt8 (f : Float.Model) : Int8 := f.unpack.toInt8

/--
Converts a `Float.Model` to an `Int16`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toInt16 (f : Float.Model) : Int16 := f.unpack.toInt16

/--
Converts a `Float.Model` to an `Int32`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toInt32 (f : Float.Model) : Int32 := f.unpack.toInt32

/--
Converts a `Float.Model` to an `Int64`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toInt64 (f : Float.Model) : Int64 := f.unpack.toInt64

/--
Converts a `Float.Model` to an `ISize`, truncating after the decimal point, sending `NaN` to
`0` and clamping out-of-range values and infinities.
-/
def toISize (f : Float.Model) : ISize := f.unpack.toISize

/-- Computes `m * 10^e`. -/
def ofScientific (m : Nat) (e : Int) : Float.Model :=
  .pack (UnpackedFloat.ofScientific Format.binary64 m e)

instance : Inhabited Float.Model where
  default := ofNat 0

end Float.Model
