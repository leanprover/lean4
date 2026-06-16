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

/-- The logical model for the `Float32` type. -/
structure Float32.Model where
  /-- The underlying bit pattern of the `Float32`. -/
  toBits : UInt32
  /-- The underlying bit pattern is valid according to the format. -/
  valid : Float.Model.Format.binary32.Valid toBits.toBitVec

namespace Float32.Model

open Float.Model (Format UnpackedFloat)

/-- Unpack a `Float32.Model` into the corresponding `UnpackedFloat`. -/
def unpack (f : Float32.Model) : UnpackedFloat :=
  UnpackedFloat.unpack Format.binary32 f.toBits.toBitVec

/--
Pack an `UnpackedFloat` into the corresponding `Float32.Model`.
This operation only gives a meaningful result if the float is
already correctly rounded for the `Format.binary32` format.
-/
def pack (f : UnpackedFloat) : Float32.Model where
  toBits := UInt32.ofBitVec (UnpackedFloat.pack Format.binary32 f)
  valid := by simp

/--
Compute the sum of two `Float32.Model`.
-/
def add (a b : Float32.Model) : Float32.Model :=
  pack (UnpackedFloat.add Format.binary32 a.unpack b.unpack)

/--
Compute the difference of two `Float32.Model`.
-/
def sub (a b : Float32.Model) : Float32.Model :=
  pack (UnpackedFloat.sub Format.binary32 a.unpack b.unpack)

/--
Compute the product of two `Float32.Model`.
-/
def mul (a b : Float32.Model) : Float32.Model :=
  pack (UnpackedFloat.mul Format.binary32 a.unpack b.unpack)

/--
Compute the quotient of two `Float32.Model`.
-/
def div (a b : Float32.Model) : Float32.Model :=
  pack (UnpackedFloat.div Format.binary32 a.unpack b.unpack)

instance : Add Float32.Model where
  add a b := a.add b

instance : Sub Float32.Model where
  sub a b := a.sub b

instance : Mul Float32.Model where
  mul a b := a.mul b

instance : Div Float32.Model where
  div a b := a.div b

/--
Compute the square root of a `Float32.Model`.
-/
def sqrt (a : Float32.Model) : Float32.Model :=
  pack (UnpackedFloat.sqrt Format.binary32 a.unpack)

/--
Negate a `Float32.Model`.
-/
def neg (a : Float32.Model) : Float32.Model :=
  pack a.unpack.neg

/--
Return a `Float32.Model` with positive sign.
-/
def abs (a : Float32.Model) : Float32.Model :=
  pack a.unpack.abs

/--
Compute the ordering between two `Float32.Model` as specified by IEEE. Returns an
`Option Ordering` to account for the fact that `NaN` is incomparable with everything.
Also, positive and negative zero are equal.
-/
protected def compare (a b : Float32.Model) : Option Ordering :=
  a.unpack.compare b.unpack

/--
Determine whether `a` is less than or equal to `b` according to IEEE rules.

This is not a total ordering, and `≤` is not reflexive.
-/
protected def le (a b : Float32.Model) : Bool :=
  a.unpack.le b.unpack

/--
Determine whether `a` is less than `b` according to IEEE rules.

This is not a total ordering.
-/
protected def lt (a b : Float32.Model) : Bool :=
  a.unpack.lt b.unpack

/--
Determine whether `a` is equal to `b` according to IEEE rules.

This is not a reflexive relation.
-/
protected def beq (a b : Float32.Model) : Bool :=
  a.unpack.beq b.unpack

instance : LE Float32.Model where
  le a b := a.le b

instance : DecidableLE Float32.Model :=
  inferInstanceAs (∀ (a b : Float32.Model), Decidable (a.le b))

instance : LT Float32.Model where
  lt a b := a.lt b

instance : DecidableLT Float32.Model :=
  inferInstanceAs (∀ (a b : Float32.Model), Decidable (a.lt b))

instance : BEq Float32.Model where
  beq a b := a.beq b

instance : Min Float32.Model :=
  Min.leftLeaningOfLE _

instance : Max Float32.Model :=
  Max.leftLeaningOfLE _

/--
Returns `true` if the float represents a real number, i.e., it is neither infinite nor `NaN`.
-/
def isFinite (a : Float32.Model) : Bool :=
  a.unpack.isFinite

/--
Returns `true` if the float is positive or negative infinity.
-/
def isInf (a : Float32.Model) : Bool :=
  a.unpack.isInf

/--
Returns `true` if the float is `NaN`.
-/
def isNaN (a : Float32.Model) : Bool :=
  a.unpack.isNaN

/--
Construct a `Float32.Model` from its bit representation. This operation canonicalizes
all `NaN` inputs into the canonical `NaN`.
-/
def ofBits (a : UInt32) : Float32.Model :=
  pack (UnpackedFloat.unpack Format.binary32 a.toBitVec)

end Float32.Model
