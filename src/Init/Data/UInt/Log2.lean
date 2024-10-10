/-
Copyright (c) 2022 Henrik Böving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Fin.Log2

@[extern "lean_uint8_log2"]
def UInt8.log2 (a : UInt8) : UInt8 := ⟨⟨Fin.log2 a.val⟩⟩

@[extern "lean_uint16_log2"]
def UInt16.log2 (a : UInt16) : UInt16 := ⟨⟨Fin.log2 a.val⟩⟩

@[extern "lean_uint32_log2"]
def UInt32.log2 (a : UInt32) : UInt32 := ⟨⟨Fin.log2 a.val⟩⟩

@[extern "lean_uint64_log2"]
def UInt64.log2 (a : UInt64) : UInt64 := ⟨⟨Fin.log2 a.val⟩⟩

@[extern "lean_usize_log2"]
def USize.log2 (a : USize) : USize := ⟨⟨Fin.log2 a.val⟩⟩
