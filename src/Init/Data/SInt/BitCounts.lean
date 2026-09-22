/-
Copyright (c) 2026 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Data.SInt.Basic
public import Init.Data.UInt.BitCounts
import Init.Data.SInt.Lemmas
import Init.Data.SInt.IntToBitVec
import Init.Data.UInt.IntToBitVec

public section

/-! Zero counts for the two's-complement representation of signed machine integers. -/

/--
Count the trailing zero bits of the two's-complement representation, returning
8 on zero. The count is unsigned.

See `Int8.ctz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def Int8.ctz (x : Int8) : UInt8 := x.toUInt8.ctz

@[simp, int_toBitVec]
theorem Int8.toBitVec_ctz (x : Int8) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `Int8.ctz`. -/
theorem Int8.toNat_ctz (x : Int8) : x.ctz.toNat =
    if x.toUInt8 = 0 then 8 else x.toUInt8.toNat.trailingZeros := UInt8.toNat_ctz x.toUInt8

/-- Expresses `Int8.ctz` through the unsigned representation. -/
theorem Int8.ctz_def (x : Int8) : x.ctz = UInt8.ofNat
    (if x.toUInt8 = 0 then 8 else x.toUInt8.toNat.trailingZeros) := UInt8.ctz_def x.toUInt8

/--
Count the leading zero bits of the two's-complement representation, returning
8 on zero. The count is unsigned.

See `Int8.clz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def Int8.clz (x : Int8) : UInt8 := x.toUInt8.clz

@[simp, int_toBitVec]
theorem Int8.toBitVec_clz (x : Int8) : x.clz.toBitVec = x.toBitVec.clz :=
  UInt8.toBitVec_clz x.toUInt8

/-- The natural-number specification of `Int8.clz`. -/
theorem Int8.toNat_clz (x : Int8) : x.clz.toNat =
    if x.toUInt8 = 0 then 8 else 8 - (x.toUInt8.toNat.log2 + 1) := UInt8.toNat_clz x.toUInt8

/-- Expresses `Int8.clz` through the unsigned representation. -/
theorem Int8.clz_def (x : Int8) : x.clz = UInt8.ofNat
    (if x.toUInt8 = 0 then 8 else 8 - (x.toUInt8.toNat.log2 + 1)) := UInt8.clz_def x.toUInt8

/--
Count the trailing zero bits of the two's-complement representation, returning
16 on zero. The count is unsigned.

See `Int16.ctz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def Int16.ctz (x : Int16) : UInt16 := x.toUInt16.ctz

@[simp, int_toBitVec]
theorem Int16.toBitVec_ctz (x : Int16) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `Int16.ctz`. -/
theorem Int16.toNat_ctz (x : Int16) : x.ctz.toNat =
    if x.toUInt16 = 0 then 16 else x.toUInt16.toNat.trailingZeros := UInt16.toNat_ctz x.toUInt16

/-- Expresses `Int16.ctz` through the unsigned representation. -/
theorem Int16.ctz_def (x : Int16) : x.ctz = UInt16.ofNat
    (if x.toUInt16 = 0 then 16 else x.toUInt16.toNat.trailingZeros) := UInt16.ctz_def x.toUInt16

/--
Count the leading zero bits of the two's-complement representation, returning
16 on zero. The count is unsigned.

See `Int16.clz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def Int16.clz (x : Int16) : UInt16 := x.toUInt16.clz

@[simp, int_toBitVec]
theorem Int16.toBitVec_clz (x : Int16) : x.clz.toBitVec = x.toBitVec.clz :=
  UInt16.toBitVec_clz x.toUInt16

/-- The natural-number specification of `Int16.clz`. -/
theorem Int16.toNat_clz (x : Int16) : x.clz.toNat =
    if x.toUInt16 = 0 then 16 else 16 - (x.toUInt16.toNat.log2 + 1) := UInt16.toNat_clz x.toUInt16

/-- Expresses `Int16.clz` through the unsigned representation. -/
theorem Int16.clz_def (x : Int16) : x.clz = UInt16.ofNat
    (if x.toUInt16 = 0 then 16 else 16 - (x.toUInt16.toNat.log2 + 1)) := UInt16.clz_def x.toUInt16

/--
Count the trailing zero bits of the two's-complement representation, returning
32 on zero. The count is unsigned.

See `Int32.ctz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def Int32.ctz (x : Int32) : UInt32 := x.toUInt32.ctz

@[simp, int_toBitVec]
theorem Int32.toBitVec_ctz (x : Int32) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `Int32.ctz`. -/
theorem Int32.toNat_ctz (x : Int32) : x.ctz.toNat =
    if x.toUInt32 = 0 then 32 else x.toUInt32.toNat.trailingZeros := UInt32.toNat_ctz x.toUInt32

/-- Expresses `Int32.ctz` through the unsigned representation. -/
theorem Int32.ctz_def (x : Int32) : x.ctz = UInt32.ofNat
    (if x.toUInt32 = 0 then 32 else x.toUInt32.toNat.trailingZeros) := UInt32.ctz_def x.toUInt32

/--
Count the leading zero bits of the two's-complement representation, returning
32 on zero. The count is unsigned.

See `Int32.clz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def Int32.clz (x : Int32) : UInt32 := x.toUInt32.clz

@[simp, int_toBitVec]
theorem Int32.toBitVec_clz (x : Int32) : x.clz.toBitVec = x.toBitVec.clz :=
  UInt32.toBitVec_clz x.toUInt32

/-- The natural-number specification of `Int32.clz`. -/
theorem Int32.toNat_clz (x : Int32) : x.clz.toNat =
    if x.toUInt32 = 0 then 32 else 32 - (x.toUInt32.toNat.log2 + 1) := UInt32.toNat_clz x.toUInt32

/-- Expresses `Int32.clz` through the unsigned representation. -/
theorem Int32.clz_def (x : Int32) : x.clz = UInt32.ofNat
    (if x.toUInt32 = 0 then 32 else 32 - (x.toUInt32.toNat.log2 + 1)) := UInt32.clz_def x.toUInt32

/--
Count the trailing zero bits of the two's-complement representation, returning
64 on zero. The count is unsigned.

See `Int64.ctz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def Int64.ctz (x : Int64) : UInt64 := x.toUInt64.ctz

@[simp, int_toBitVec]
theorem Int64.toBitVec_ctz (x : Int64) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `Int64.ctz`. -/
theorem Int64.toNat_ctz (x : Int64) : x.ctz.toNat =
    if x.toUInt64 = 0 then 64 else x.toUInt64.toNat.trailingZeros := UInt64.toNat_ctz x.toUInt64

/-- Expresses `Int64.ctz` through the unsigned representation. -/
theorem Int64.ctz_def (x : Int64) : x.ctz = UInt64.ofNat
    (if x.toUInt64 = 0 then 64 else x.toUInt64.toNat.trailingZeros) := UInt64.ctz_def x.toUInt64

/--
Count the leading zero bits of the two's-complement representation, returning
64 on zero. The count is unsigned.

See `Int64.clz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def Int64.clz (x : Int64) : UInt64 := x.toUInt64.clz

@[simp, int_toBitVec]
theorem Int64.toBitVec_clz (x : Int64) : x.clz.toBitVec = x.toBitVec.clz :=
  UInt64.toBitVec_clz x.toUInt64

/-- The natural-number specification of `Int64.clz`. -/
theorem Int64.toNat_clz (x : Int64) : x.clz.toNat =
    if x.toUInt64 = 0 then 64 else 64 - (x.toUInt64.toNat.log2 + 1) := UInt64.toNat_clz x.toUInt64

/-- Expresses `Int64.clz` through the unsigned representation. -/
theorem Int64.clz_def (x : Int64) : x.clz = UInt64.ofNat
    (if x.toUInt64 = 0 then 64 else 64 - (x.toUInt64.toNat.log2 + 1)) := UInt64.clz_def x.toUInt64

/--
Count the trailing zero bits of the two's-complement representation, returning
the platform word width on zero. The count is unsigned.

See `ISize.ctz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def ISize.ctz (x : ISize) : USize := x.toUSize.ctz

@[simp]
theorem ISize.toBitVec_ctz (x : ISize) : x.ctz.toBitVec = x.toBitVec.ctz := rfl

/-- The natural-number specification of `ISize.ctz`. -/
theorem ISize.toNat_ctz (x : ISize) : x.ctz.toNat =
    if x.toUSize = 0 then System.Platform.numBits else x.toUSize.toNat.trailingZeros := USize.toNat_ctz x.toUSize

/-- Expresses `ISize.ctz` through the unsigned representation. -/
theorem ISize.ctz_def (x : ISize) : x.ctz = USize.ofNat
    (if x.toUSize = 0 then System.Platform.numBits else x.toUSize.toNat.trailingZeros) := USize.ctz_def x.toUSize

/--
Count the leading zero bits of the two's-complement representation, returning
the platform word width on zero. The count is unsigned.

See `ISize.clz_def` for the specification via the unsigned natural value.
-/
@[expose, inline]
def ISize.clz (x : ISize) : USize := x.toUSize.clz

@[simp]
theorem ISize.toBitVec_clz (x : ISize) : x.clz.toBitVec = x.toBitVec.clz :=
  USize.toBitVec_clz x.toUSize

/-- The natural-number specification of `ISize.clz`. -/
theorem ISize.toNat_clz (x : ISize) : x.clz.toNat =
    if x.toUSize = 0 then System.Platform.numBits else System.Platform.numBits - (x.toUSize.toNat.log2 + 1) := USize.toNat_clz x.toUSize

/-- Expresses `ISize.clz` through the unsigned representation. -/
theorem ISize.clz_def (x : ISize) : x.clz = USize.ofNat
    (if x.toUSize = 0 then System.Platform.numBits else System.Platform.numBits - (x.toUSize.toNat.log2 + 1)) := USize.clz_def x.toUSize

@[int_toBitVec]
theorem ISize.toBitVec32_ctz (x : ISize) (h : System.Platform.numBits = 32) :
    x.ctz.toBitVec32 h = (x.toBitVec32 h).ctz := by
  simp only [USize.toBitVec32_eq_toBitVec, ISize.toBitVec32_eq_toBitVec, ISize.toBitVec_ctz]
  generalize 32 = n at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_clz (x : ISize) (h : System.Platform.numBits = 32) :
    x.clz.toBitVec32 h = (x.toBitVec32 h).clz := by
  simp only [USize.toBitVec32_eq_toBitVec, ISize.toBitVec32_eq_toBitVec, ISize.toBitVec_clz]
  generalize 32 = n at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_ctz (x : ISize) (h : System.Platform.numBits = 64) :
    x.ctz.toBitVec64 h = (x.toBitVec64 h).ctz := by
  simp only [USize.toBitVec64_eq_toBitVec, ISize.toBitVec64_eq_toBitVec, ISize.toBitVec_ctz]
  generalize 64 = n at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_clz (x : ISize) (h : System.Platform.numBits = 64) :
    x.clz.toBitVec64 h = (x.toBitVec64 h).clz := by
  simp only [USize.toBitVec64_eq_toBitVec, ISize.toBitVec64_eq_toBitVec, ISize.toBitVec_clz]
  generalize 64 = n at *
  subst h
  rfl

