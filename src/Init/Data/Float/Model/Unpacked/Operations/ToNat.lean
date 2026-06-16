/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Float.Model.Unpacked.Round
public import Init.Data.SInt.Basic

-- This file is part of the logical model for floats which authors of float libraries
-- need to rely on.
@[expose] public section

namespace Float.Model.UnpackedFloat

/--
Returns an `Int` that is close to the given `(sign, mantissa, exponent)` triple.
-/
def roundToInt (sign : Sign) (mantissa : Nat) (exponent : Int) : Int :=
  let (mantissa, exponent) := decreaseExponent mantissa exponent 0
  let (em₁, _) := shiftToExponent mantissa exponent .exact 0
  sign.apply em₁.mantissa

/-- Converts an `UnpackedFloat` to an `Int`. -/
def toInt (negativeInfinity positiveInfinity : Int) : UnpackedFloat → Int
  | .notANumber => 0
  | .infinity .positive => positiveInfinity
  | .infinity .negative => negativeInfinity
  | .zero _ => 0
  | .finite s m e _ => roundToInt s m e

/-- Converts an `UnpackedFloat` to a `UInt8`. -/
def toUInt8 (f : UnpackedFloat) : UInt8 :=
  UInt8.ofNatClamp (f.toInt 0 (UInt8.size - 1)).toNat

/-- Converts an `UnpackedFloat` to a `UInt16`. -/
def toUInt16 (f : UnpackedFloat) : UInt16 :=
  UInt16.ofNatClamp (f.toInt 0 (UInt16.size - 1)).toNat

/-- Converts an `UnpackedFloat` to a `UInt32`. -/
def toUInt32 (f : UnpackedFloat) : UInt32 :=
  UInt32.ofNatClamp (f.toInt 0 (UInt32.size - 1)).toNat

/-- Converts an `UnpackedFloat` to a `UInt64`. -/
def toUInt64 (f : UnpackedFloat) : UInt64 :=
  UInt64.ofNatClamp (f.toInt 0 (UInt64.size - 1)).toNat

/-- Converts an `UnpackedFloat` to a `USize`. -/
def toUSize (f : UnpackedFloat) : USize :=
  USize.ofNatClamp (f.toInt 0 (USize.size - 1)).toNat

/-- Converts an `UnpackedFloat` to an `Int8`. -/
def toInt8 (f : UnpackedFloat) : Int8 :=
  Int8.ofIntClamp (f.toInt Int8.minValue.toInt Int8.maxValue.toInt)

/-- Converts an `UnpackedFloat` to an `Int16`. -/
def toInt16 (f : UnpackedFloat) : Int16 :=
  Int16.ofIntClamp (f.toInt Int16.minValue.toInt Int16.maxValue.toInt)

/-- Converts an `UnpackedFloat` to an `Int32`. -/
def toInt32 (f : UnpackedFloat) : Int32 :=
  Int32.ofIntClamp (f.toInt Int32.minValue.toInt Int32.maxValue.toInt)

/-- Converts an `UnpackedFloat` to an `Int64`. -/
def toInt64 (f : UnpackedFloat) : Int64 :=
  Int64.ofIntClamp (f.toInt Int64.minValue.toInt Int64.maxValue.toInt)

/-- Converts an `UnpackedFloat` to an `ISize`. -/
def toISize (f : UnpackedFloat) : ISize :=
  ISize.ofIntClamp (f.toInt ISize.minValue.toInt ISize.maxValue.toInt)
