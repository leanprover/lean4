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
