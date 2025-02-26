/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
prelude
import Init.Data.SInt.Basic

@[simp] theorem UInt8.toBitVec_toInt8 (x : UInt8) : x.toInt8.toBitVec = x.toBitVec := rfl
@[simp] theorem UInt16.toBitVec_toInt16 (x : UInt16) : x.toInt16.toBitVec = x.toBitVec := rfl
@[simp] theorem UInt32.toBitVec_toInt32 (x : UInt32) : x.toInt32.toBitVec = x.toBitVec := rfl
@[simp] theorem UInt64.toBitVec_toInt64 (x : UInt64) : x.toInt64.toBitVec = x.toBitVec := rfl
@[simp] theorem USize.toBitVec_toISize (x : USize) : x.toISize.toBitVec = x.toBitVec := rfl

@[simp] theorem Int8.ofBitVec_uInt8ToBitVec (x : UInt8) : Int8.ofBitVec x.toBitVec = x.toInt8 := rfl
@[simp] theorem Int16.ofBitVec_uInt16ToBitVec (x : UInt16) : Int16.ofBitVec x.toBitVec = x.toInt16 := rfl
@[simp] theorem Int32.ofBitVec_uInt32ToBitVec (x : UInt32) : Int32.ofBitVec x.toBitVec = x.toInt32 := rfl
@[simp] theorem Int64.ofBitVec_uInt64ToBitVec (x : UInt64) : Int64.ofBitVec x.toBitVec = x.toInt64 := rfl
@[simp] theorem ISize.ofBitVec_uSize8ToBitVec (x : USize) : ISize.ofBitVec x.toBitVec = x.toISize := rfl

@[simp] theorem UInt8.toUInt8_toInt8 (x : UInt8) : x.toInt8.toUInt8 = x := rfl
@[simp] theorem UInt16.toUInt16_toInt16 (x : UInt16) : x.toInt16.toUInt16 = x := rfl
@[simp] theorem UInt32.toUInt32_toInt32 (x : UInt32) : x.toInt32.toUInt32 = x := rfl
@[simp] theorem UInt64.toUInt64_toInt64 (x : UInt64) : x.toInt64.toUInt64 = x := rfl
@[simp] theorem USize.toUSize_toISize (x : USize) : x.toISize.toUSize = x := rfl
