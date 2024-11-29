/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.UInt.BasicAux
import Init.Data.BitVec.Basic

open Nat

@[extern "lean_uint8_add"]
def UInt8.add (a b : UInt8) : UInt8 := ⟨a.toBitVec + b.toBitVec⟩
@[extern "lean_uint8_sub"]
def UInt8.sub (a b : UInt8) : UInt8 := ⟨a.toBitVec - b.toBitVec⟩
@[extern "lean_uint8_mul"]
def UInt8.mul (a b : UInt8) : UInt8 := ⟨a.toBitVec * b.toBitVec⟩
@[extern "lean_uint8_div"]
def UInt8.div (a b : UInt8) : UInt8 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
@[extern "lean_uint8_mod"]
def UInt8.mod (a b : UInt8) : UInt8 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
@[deprecated UInt8.mod (since := "2024-09-23")]
def UInt8.modn (a : UInt8) (n : Nat) : UInt8 := ⟨Fin.modn a.val n⟩
@[extern "lean_uint8_land"]
def UInt8.land (a b : UInt8) : UInt8 := ⟨a.toBitVec &&& b.toBitVec⟩
@[extern "lean_uint8_lor"]
def UInt8.lor (a b : UInt8) : UInt8 := ⟨a.toBitVec ||| b.toBitVec⟩
@[extern "lean_uint8_xor"]
def UInt8.xor (a b : UInt8) : UInt8 := ⟨a.toBitVec ^^^ b.toBitVec⟩
@[extern "lean_uint8_shift_left"]
def UInt8.shiftLeft (a b : UInt8) : UInt8 := ⟨a.toBitVec <<< (mod b 8).toBitVec⟩
@[extern "lean_uint8_shift_right"]
def UInt8.shiftRight (a b : UInt8) : UInt8 := ⟨a.toBitVec >>> (mod b 8).toBitVec⟩
def UInt8.lt (a b : UInt8) : Prop := a.toBitVec < b.toBitVec
def UInt8.le (a b : UInt8) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add UInt8       := ⟨UInt8.add⟩
instance : Sub UInt8       := ⟨UInt8.sub⟩
instance : Mul UInt8       := ⟨UInt8.mul⟩
instance : Mod UInt8       := ⟨UInt8.mod⟩

set_option linter.deprecated false in
instance : HMod UInt8 Nat UInt8 := ⟨UInt8.modn⟩

instance : Div UInt8       := ⟨UInt8.div⟩
instance : LT UInt8        := ⟨UInt8.lt⟩
instance : LE UInt8        := ⟨UInt8.le⟩

@[extern "lean_uint8_complement"]
def UInt8.complement (a : UInt8) : UInt8 := ⟨~~~a.toBitVec⟩

instance : Complement UInt8 := ⟨UInt8.complement⟩
instance : AndOp UInt8     := ⟨UInt8.land⟩
instance : OrOp UInt8      := ⟨UInt8.lor⟩
instance : Xor UInt8       := ⟨UInt8.xor⟩
instance : ShiftLeft UInt8  := ⟨UInt8.shiftLeft⟩
instance : ShiftRight UInt8 := ⟨UInt8.shiftRight⟩

@[extern "lean_bool_to_uint8"]
def Bool.toUInt8 (b : Bool) : UInt8 := if b then 1 else 0

@[extern "lean_uint8_dec_lt"]
def UInt8.decLt (a b : UInt8) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

@[extern "lean_uint8_dec_le"]
def UInt8.decLe (a b : UInt8) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

instance (a b : UInt8) : Decidable (a < b) := UInt8.decLt a b
instance (a b : UInt8) : Decidable (a ≤ b) := UInt8.decLe a b
instance : Max UInt8 := maxOfLe
instance : Min UInt8 := minOfLe

@[extern "lean_uint16_add"]
def UInt16.add (a b : UInt16) : UInt16 := ⟨a.toBitVec + b.toBitVec⟩
@[extern "lean_uint16_sub"]
def UInt16.sub (a b : UInt16) : UInt16 := ⟨a.toBitVec - b.toBitVec⟩
@[extern "lean_uint16_mul"]
def UInt16.mul (a b : UInt16) : UInt16 := ⟨a.toBitVec * b.toBitVec⟩
@[extern "lean_uint16_div"]
def UInt16.div (a b : UInt16) : UInt16 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
@[extern "lean_uint16_mod"]
def UInt16.mod (a b : UInt16) : UInt16 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
@[deprecated UInt16.mod (since := "2024-09-23")]
def UInt16.modn (a : UInt16) (n : Nat) : UInt16 := ⟨Fin.modn a.val n⟩
@[extern "lean_uint16_land"]
def UInt16.land (a b : UInt16) : UInt16 := ⟨a.toBitVec &&& b.toBitVec⟩
@[extern "lean_uint16_lor"]
def UInt16.lor (a b : UInt16) : UInt16 := ⟨a.toBitVec ||| b.toBitVec⟩
@[extern "lean_uint16_xor"]
def UInt16.xor (a b : UInt16) : UInt16 := ⟨a.toBitVec ^^^ b.toBitVec⟩
@[extern "lean_uint16_shift_left"]
def UInt16.shiftLeft (a b : UInt16) : UInt16 := ⟨a.toBitVec <<< (mod b 16).toBitVec⟩
@[extern "lean_uint16_shift_right"]
def UInt16.shiftRight (a b : UInt16) : UInt16 := ⟨a.toBitVec >>> (mod b 16).toBitVec⟩
def UInt16.lt (a b : UInt16) : Prop := a.toBitVec < b.toBitVec
def UInt16.le (a b : UInt16) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add UInt16       := ⟨UInt16.add⟩
instance : Sub UInt16       := ⟨UInt16.sub⟩
instance : Mul UInt16       := ⟨UInt16.mul⟩
instance : Mod UInt16       := ⟨UInt16.mod⟩

set_option linter.deprecated false in
instance : HMod UInt16 Nat UInt16 := ⟨UInt16.modn⟩

instance : Div UInt16       := ⟨UInt16.div⟩
instance : LT UInt16        := ⟨UInt16.lt⟩
instance : LE UInt16        := ⟨UInt16.le⟩

@[extern "lean_uint16_complement"]
def UInt16.complement (a : UInt16) : UInt16 := ⟨~~~a.toBitVec⟩

instance : Complement UInt16 := ⟨UInt16.complement⟩
instance : AndOp UInt16     := ⟨UInt16.land⟩
instance : OrOp UInt16      := ⟨UInt16.lor⟩
instance : Xor UInt16       := ⟨UInt16.xor⟩
instance : ShiftLeft UInt16  := ⟨UInt16.shiftLeft⟩
instance : ShiftRight UInt16 := ⟨UInt16.shiftRight⟩

@[extern "lean_bool_to_uint16"]
def Bool.toUInt16 (b : Bool) : UInt16 := if b then 1 else 0

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint16_dec_lt"]
def UInt16.decLt (a b : UInt16) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint16_dec_le"]
def UInt16.decLe (a b : UInt16) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

instance (a b : UInt16) : Decidable (a < b) := UInt16.decLt a b
instance (a b : UInt16) : Decidable (a ≤ b) := UInt16.decLe a b
instance : Max UInt16 := maxOfLe
instance : Min UInt16 := minOfLe

@[extern "lean_uint32_add"]
def UInt32.add (a b : UInt32) : UInt32 := ⟨a.toBitVec + b.toBitVec⟩
@[extern "lean_uint32_sub"]
def UInt32.sub (a b : UInt32) : UInt32 := ⟨a.toBitVec - b.toBitVec⟩
@[extern "lean_uint32_mul"]
def UInt32.mul (a b : UInt32) : UInt32 := ⟨a.toBitVec * b.toBitVec⟩
@[extern "lean_uint32_div"]
def UInt32.div (a b : UInt32) : UInt32 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
@[extern "lean_uint32_mod"]
def UInt32.mod (a b : UInt32) : UInt32 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
@[deprecated UInt32.mod (since := "2024-09-23")]
def UInt32.modn (a : UInt32) (n : Nat) : UInt32 := ⟨Fin.modn a.val n⟩
@[extern "lean_uint32_land"]
def UInt32.land (a b : UInt32) : UInt32 := ⟨a.toBitVec &&& b.toBitVec⟩
@[extern "lean_uint32_lor"]
def UInt32.lor (a b : UInt32) : UInt32 := ⟨a.toBitVec ||| b.toBitVec⟩
@[extern "lean_uint32_xor"]
def UInt32.xor (a b : UInt32) : UInt32 := ⟨a.toBitVec ^^^ b.toBitVec⟩
@[extern "lean_uint32_shift_left"]
def UInt32.shiftLeft (a b : UInt32) : UInt32 := ⟨a.toBitVec <<< (mod b 32).toBitVec⟩
@[extern "lean_uint32_shift_right"]
def UInt32.shiftRight (a b : UInt32) : UInt32 := ⟨a.toBitVec >>> (mod b 32).toBitVec⟩

instance : Add UInt32       := ⟨UInt32.add⟩
instance : Sub UInt32       := ⟨UInt32.sub⟩
instance : Mul UInt32       := ⟨UInt32.mul⟩
instance : Mod UInt32       := ⟨UInt32.mod⟩

set_option linter.deprecated false in
instance : HMod UInt32 Nat UInt32 := ⟨UInt32.modn⟩

instance : Div UInt32       := ⟨UInt32.div⟩

@[extern "lean_uint32_complement"]
def UInt32.complement (a : UInt32) : UInt32 := ⟨~~~a.toBitVec⟩

instance : Complement UInt32 := ⟨UInt32.complement⟩
instance : AndOp UInt32     := ⟨UInt32.land⟩
instance : OrOp UInt32      := ⟨UInt32.lor⟩
instance : Xor UInt32       := ⟨UInt32.xor⟩
instance : ShiftLeft UInt32  := ⟨UInt32.shiftLeft⟩
instance : ShiftRight UInt32 := ⟨UInt32.shiftRight⟩

@[extern "lean_bool_to_uint32"]
def Bool.toUInt32 (b : Bool) : UInt32 := if b then 1 else 0

@[extern "lean_uint64_add"]
def UInt64.add (a b : UInt64) : UInt64 := ⟨a.toBitVec + b.toBitVec⟩
@[extern "lean_uint64_sub"]
def UInt64.sub (a b : UInt64) : UInt64 := ⟨a.toBitVec - b.toBitVec⟩
@[extern "lean_uint64_mul"]
def UInt64.mul (a b : UInt64) : UInt64 := ⟨a.toBitVec * b.toBitVec⟩
@[extern "lean_uint64_div"]
def UInt64.div (a b : UInt64) : UInt64 := ⟨BitVec.udiv a.toBitVec b.toBitVec⟩
@[extern "lean_uint64_mod"]
def UInt64.mod (a b : UInt64) : UInt64 := ⟨BitVec.umod a.toBitVec b.toBitVec⟩
@[deprecated UInt64.mod (since := "2024-09-23")]
def UInt64.modn (a : UInt64) (n : Nat) : UInt64 := ⟨Fin.modn a.val n⟩
@[extern "lean_uint64_land"]
def UInt64.land (a b : UInt64) : UInt64 := ⟨a.toBitVec &&& b.toBitVec⟩
@[extern "lean_uint64_lor"]
def UInt64.lor (a b : UInt64) : UInt64 := ⟨a.toBitVec ||| b.toBitVec⟩
@[extern "lean_uint64_xor"]
def UInt64.xor (a b : UInt64) : UInt64 := ⟨a.toBitVec ^^^ b.toBitVec⟩
@[extern "lean_uint64_shift_left"]
def UInt64.shiftLeft (a b : UInt64) : UInt64 := ⟨a.toBitVec <<< (mod b 64).toBitVec⟩
@[extern "lean_uint64_shift_right"]
def UInt64.shiftRight (a b : UInt64) : UInt64 := ⟨a.toBitVec >>> (mod b 64).toBitVec⟩
def UInt64.lt (a b : UInt64) : Prop := a.toBitVec < b.toBitVec
def UInt64.le (a b : UInt64) : Prop := a.toBitVec ≤ b.toBitVec

instance : Add UInt64       := ⟨UInt64.add⟩
instance : Sub UInt64       := ⟨UInt64.sub⟩
instance : Mul UInt64       := ⟨UInt64.mul⟩
instance : Mod UInt64       := ⟨UInt64.mod⟩

set_option linter.deprecated false in
instance : HMod UInt64 Nat UInt64 := ⟨UInt64.modn⟩

instance : Div UInt64       := ⟨UInt64.div⟩
instance : LT UInt64        := ⟨UInt64.lt⟩
instance : LE UInt64        := ⟨UInt64.le⟩

@[extern "lean_uint64_complement"]
def UInt64.complement (a : UInt64) : UInt64 := ⟨~~~a.toBitVec⟩

instance : Complement UInt64 := ⟨UInt64.complement⟩
instance : AndOp UInt64     := ⟨UInt64.land⟩
instance : OrOp UInt64      := ⟨UInt64.lor⟩
instance : Xor UInt64       := ⟨UInt64.xor⟩
instance : ShiftLeft UInt64  := ⟨UInt64.shiftLeft⟩
instance : ShiftRight UInt64 := ⟨UInt64.shiftRight⟩

@[extern "lean_bool_to_uint64"]
def Bool.toUInt64 (b : Bool) : UInt64 := if b then 1 else 0

@[extern "lean_uint64_dec_lt"]
def UInt64.decLt (a b : UInt64) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

@[extern "lean_uint64_dec_le"]
def UInt64.decLe (a b : UInt64) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

instance (a b : UInt64) : Decidable (a < b) := UInt64.decLt a b
instance (a b : UInt64) : Decidable (a ≤ b) := UInt64.decLe a b
instance : Max UInt64 := maxOfLe
instance : Min UInt64 := minOfLe

theorem usize_size_le : USize.size ≤ 18446744073709551616 := by
  cases usize_size_eq <;> next h => rw [h]; decide

theorem le_usize_size : 4294967296 ≤ USize.size := by
  cases usize_size_eq <;> next h => rw [h]; decide

@[extern "lean_usize_mul"]
def USize.mul (a b : USize) : USize := ⟨a.toBitVec * b.toBitVec⟩
@[extern "lean_usize_div"]
def USize.div (a b : USize) : USize := ⟨a.toBitVec / b.toBitVec⟩
@[extern "lean_usize_mod"]
def USize.mod (a b : USize) : USize := ⟨a.toBitVec % b.toBitVec⟩
@[deprecated USize.mod (since := "2024-09-23")]
def USize.modn (a : USize) (n : Nat) : USize := ⟨Fin.modn a.val n⟩
@[extern "lean_usize_land"]
def USize.land (a b : USize) : USize := ⟨a.toBitVec &&& b.toBitVec⟩
@[extern "lean_usize_lor"]
def USize.lor (a b : USize) : USize := ⟨a.toBitVec ||| b.toBitVec⟩
@[extern "lean_usize_xor"]
def USize.xor (a b : USize) : USize := ⟨a.toBitVec ^^^ b.toBitVec⟩
@[extern "lean_usize_shift_left"]
def USize.shiftLeft (a b : USize) : USize := ⟨a.toBitVec <<< (mod b (USize.ofNat System.Platform.numBits)).toBitVec⟩
@[extern "lean_usize_shift_right"]
def USize.shiftRight (a b : USize) : USize := ⟨a.toBitVec >>> (mod b (USize.ofNat System.Platform.numBits)).toBitVec⟩
/--
Upcast a `Nat` less than `2^32` to a `USize`.
This is lossless because `USize.size` is either `2^32` or `2^64`.
This function is overridden with a native implementation.
-/
@[extern "lean_usize_of_nat"]
def USize.ofNat32 (n : @& Nat) (h : n < 4294967296) : USize :=
  USize.ofNatCore n (Nat.lt_of_lt_of_le h le_usize_size)
@[extern "lean_uint8_to_usize"]
def UInt8.toUSize (a : UInt8) : USize :=
  USize.ofNat32 a.toBitVec.toNat (Nat.lt_trans a.toBitVec.isLt (by decide))
@[extern "lean_usize_to_uint8"]
def USize.toUInt8 (a : USize) : UInt8 := a.toNat.toUInt8
@[extern "lean_uint16_to_usize"]
def UInt16.toUSize (a : UInt16) : USize :=
  USize.ofNat32 a.toBitVec.toNat (Nat.lt_trans a.toBitVec.isLt (by decide))
@[extern "lean_usize_to_uint16"]
def USize.toUInt16 (a : USize) : UInt16 := a.toNat.toUInt16
@[extern "lean_uint32_to_usize"]
def UInt32.toUSize (a : UInt32) : USize := USize.ofNat32 a.toBitVec.toNat a.toBitVec.isLt
@[extern "lean_usize_to_uint32"]
def USize.toUInt32 (a : USize) : UInt32 := a.toNat.toUInt32
/-- Converts a `UInt64` to a `USize` by reducing modulo `USize.size`. -/
@[extern "lean_uint64_to_usize"]
def UInt64.toUSize (a : UInt64) : USize := a.toNat.toUSize
/--
Upcast a `USize` to a `UInt64`.
This is lossless because `USize.size` is either `2^32` or `2^64`.
This function is overridden with a native implementation.
-/
@[extern "lean_usize_to_uint64"]
def USize.toUInt64 (a : USize) : UInt64 :=
  UInt64.ofNatCore a.toBitVec.toNat (Nat.lt_of_lt_of_le a.toBitVec.isLt usize_size_le)

instance : Mul USize       := ⟨USize.mul⟩
instance : Mod USize       := ⟨USize.mod⟩

set_option linter.deprecated false in
instance : HMod USize Nat USize := ⟨USize.modn⟩

instance : Div USize       := ⟨USize.div⟩

@[extern "lean_usize_complement"]
def USize.complement (a : USize) : USize := ⟨~~~a.toBitVec⟩

instance : Complement USize := ⟨USize.complement⟩
instance : AndOp USize      := ⟨USize.land⟩
instance : OrOp USize       := ⟨USize.lor⟩
instance : Xor USize        := ⟨USize.xor⟩
instance : ShiftLeft USize  := ⟨USize.shiftLeft⟩
instance : ShiftRight USize := ⟨USize.shiftRight⟩

@[extern "lean_bool_to_usize"]
def Bool.toUSize (b : Bool) : USize := if b then 1 else 0

instance : Max USize := maxOfLe
instance : Min USize := minOfLe
