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

/-- Converts an `Int` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofInt (spec : Format) (n : Int) : UnpackedFloat :=
  normalize spec n 0 .positive

/-- Converts a `Nat` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofNat (spec : Format) (n : Nat) : UnpackedFloat :=
  ofInt spec (n : Int)

/-- Converts a `UInt8` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofUInt8 (spec : Format) (n : UInt8) : UnpackedFloat :=
  ofNat spec n.toNat

/-- Converts a `UInt16` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofUInt16 (spec : Format) (n : UInt16) : UnpackedFloat :=
  ofNat spec n.toNat

/-- Converts a `UInt32` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofUInt32 (spec : Format) (n : UInt32) : UnpackedFloat :=
  ofNat spec n.toNat

/-- Converts a `UInt64` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofUInt64 (spec : Format) (n : UInt64) : UnpackedFloat :=
  ofNat spec n.toNat

/-- Converts a `USize` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofUSize (spec : Format) (n : USize) : UnpackedFloat :=
  ofNat spec n.toNat

/-- Converts an `Int8` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofInt8 (spec : Format) (n : Int8) : UnpackedFloat :=
  ofInt spec n.toInt

/-- Converts an `Int16` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofInt16 (spec : Format) (n : Int16) : UnpackedFloat :=
  ofInt spec n.toInt

/-- Converts an `Int32` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofInt32 (spec : Format) (n : Int32) : UnpackedFloat :=
  ofInt spec n.toInt

/-- Converts an `Int64` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofInt64 (spec : Format) (n : Int64) : UnpackedFloat :=
  ofInt spec n.toInt

/-- Converts an `ISize` to an `UnpackedFloat`, returning positive zero on zero. -/
def ofISize (spec : Format) (n : ISize) : UnpackedFloat :=
  ofInt spec n.toInt

end Float.Model.UnpackedFloat
