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

/-- The logical model for the `Float` type. -/
structure Float.Model where
  /-- The underlying bit pattern of the `Float`. -/
  toBits : UInt64
  /-- The underlying bit pattern is valid according to the format. -/
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

end Float.Model
