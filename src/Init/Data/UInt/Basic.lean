/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Fin.Basic
import Init.System.Platform

open Nat

@[extern "lean_uint8_of_nat"]
def UInt8.ofNat (n : @& Nat) : UInt8 := ⟨Fin.ofNat n⟩
abbrev Nat.toUInt8 := UInt8.ofNat
@[extern "lean_uint8_to_nat"]
def UInt8.toNat (n : UInt8) : Nat := n.val.val
@[extern "lean_uint8_add"]
def UInt8.add (a b : UInt8) : UInt8 := ⟨a.val + b.val⟩
@[extern "lean_uint8_sub"]
def UInt8.sub (a b : UInt8) : UInt8 := ⟨a.val - b.val⟩
@[extern "lean_uint8_mul"]
def UInt8.mul (a b : UInt8) : UInt8 := ⟨a.val * b.val⟩
@[extern "lean_uint8_div"]
def UInt8.div (a b : UInt8) : UInt8 := ⟨a.val / b.val⟩
@[extern "lean_uint8_mod"]
def UInt8.mod (a b : UInt8) : UInt8 := ⟨a.val % b.val⟩
@[extern "lean_uint8_modn"]
def UInt8.modn (a : UInt8) (n : @& Nat) : UInt8 := ⟨Fin.modn a.val n⟩
@[extern "lean_uint8_land"]
def UInt8.land (a b : UInt8) : UInt8 := ⟨Fin.land a.val b.val⟩
@[extern "lean_uint8_lor"]
def UInt8.lor (a b : UInt8) : UInt8 := ⟨Fin.lor a.val b.val⟩
@[extern "lean_uint8_xor"]
def UInt8.xor (a b : UInt8) : UInt8 := ⟨Fin.xor a.val b.val⟩
@[extern "lean_uint8_shift_left"]
def UInt8.shiftLeft (a b : UInt8) : UInt8 := ⟨a.val <<< (modn b 8).val⟩
@[extern "lean_uint8_shift_right"]
def UInt8.shiftRight (a b : UInt8) : UInt8 := ⟨a.val >>> (modn b 8).val⟩
def UInt8.lt (a b : UInt8) : Prop := a.val < b.val
def UInt8.le (a b : UInt8) : Prop := a.val ≤ b.val

instance : OfNat UInt8 n   := ⟨UInt8.ofNat n⟩
instance : Add UInt8       := ⟨UInt8.add⟩
instance : Sub UInt8       := ⟨UInt8.sub⟩
instance : Mul UInt8       := ⟨UInt8.mul⟩
instance : Mod UInt8       := ⟨UInt8.mod⟩
instance : HMod UInt8 Nat UInt8 := ⟨UInt8.modn⟩
instance : Div UInt8       := ⟨UInt8.div⟩
instance : LT UInt8        := ⟨UInt8.lt⟩
instance : LE UInt8        := ⟨UInt8.le⟩

@[extern "lean_uint8_complement"]
def UInt8.complement (a:UInt8) : UInt8 := 0-(a+1)

instance : Complement UInt8 := ⟨UInt8.complement⟩
instance : AndOp UInt8     := ⟨UInt8.land⟩
instance : OrOp UInt8      := ⟨UInt8.lor⟩
instance : Xor UInt8       := ⟨UInt8.xor⟩
instance : ShiftLeft UInt8  := ⟨UInt8.shiftLeft⟩
instance : ShiftRight UInt8 := ⟨UInt8.shiftRight⟩

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint8_dec_lt"]
def UInt8.decLt (a b : UInt8) : Decidable (a < b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n < m))

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint8_dec_le"]
def UInt8.decLe (a b : UInt8) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n <= m))

instance (a b : UInt8) : Decidable (a < b) := UInt8.decLt a b
instance (a b : UInt8) : Decidable (a ≤ b) := UInt8.decLe a b
instance : Max UInt8 := maxOfLe
instance : Min UInt8 := minOfLe

@[extern "lean_uint16_of_nat"]
def UInt16.ofNat (n : @& Nat) : UInt16 := ⟨Fin.ofNat n⟩
abbrev Nat.toUInt16 := UInt16.ofNat
@[extern "lean_uint16_to_nat"]
def UInt16.toNat (n : UInt16) : Nat := n.val.val
@[extern "lean_uint16_add"]
def UInt16.add (a b : UInt16) : UInt16 := ⟨a.val + b.val⟩
@[extern "lean_uint16_sub"]
def UInt16.sub (a b : UInt16) : UInt16 := ⟨a.val - b.val⟩
@[extern "lean_uint16_mul"]
def UInt16.mul (a b : UInt16) : UInt16 := ⟨a.val * b.val⟩
@[extern "lean_uint16_div"]
def UInt16.div (a b : UInt16) : UInt16 := ⟨a.val / b.val⟩
@[extern "lean_uint16_mod"]
def UInt16.mod (a b : UInt16) : UInt16 := ⟨a.val % b.val⟩
@[extern "lean_uint16_modn"]
def UInt16.modn (a : UInt16) (n : @& Nat) : UInt16 := ⟨Fin.modn a.val n⟩
@[extern "lean_uint16_land"]
def UInt16.land (a b : UInt16) : UInt16 := ⟨Fin.land a.val b.val⟩
@[extern "lean_uint16_lor"]
def UInt16.lor (a b : UInt16) : UInt16 := ⟨Fin.lor a.val b.val⟩
@[extern "lean_uint16_xor"]
def UInt16.xor (a b : UInt16) : UInt16 := ⟨Fin.xor a.val b.val⟩
@[extern "lean_uint16_shift_left"]
def UInt16.shiftLeft (a b : UInt16) : UInt16 := ⟨a.val <<< (modn b 16).val⟩
@[extern "lean_uint16_to_uint8"]
def UInt16.toUInt8 (a : UInt16) : UInt8 := a.toNat.toUInt8
@[extern "lean_uint8_to_uint16"]
def UInt8.toUInt16 (a : UInt8) : UInt16 := a.toNat.toUInt16
@[extern "lean_uint16_shift_right"]
def UInt16.shiftRight (a b : UInt16) : UInt16 := ⟨a.val >>> (modn b 16).val⟩
def UInt16.lt (a b : UInt16) : Prop := a.val < b.val
def UInt16.le (a b : UInt16) : Prop := a.val ≤ b.val


instance : OfNat UInt16 n   := ⟨UInt16.ofNat n⟩
instance : Add UInt16       := ⟨UInt16.add⟩
instance : Sub UInt16       := ⟨UInt16.sub⟩
instance : Mul UInt16       := ⟨UInt16.mul⟩
instance : Mod UInt16       := ⟨UInt16.mod⟩
instance : HMod UInt16 Nat UInt16 := ⟨UInt16.modn⟩
instance : Div UInt16       := ⟨UInt16.div⟩
instance : LT UInt16        := ⟨UInt16.lt⟩
instance : LE UInt16        := ⟨UInt16.le⟩

@[extern "lean_uint16_complement"]
def UInt16.complement (a:UInt16) : UInt16 := 0-(a+1)

instance : Complement UInt16 := ⟨UInt16.complement⟩
instance : AndOp UInt16     := ⟨UInt16.land⟩
instance : OrOp UInt16      := ⟨UInt16.lor⟩
instance : Xor UInt16       := ⟨UInt16.xor⟩
instance : ShiftLeft UInt16  := ⟨UInt16.shiftLeft⟩
instance : ShiftRight UInt16 := ⟨UInt16.shiftRight⟩

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint16_dec_lt"]
def UInt16.decLt (a b : UInt16) : Decidable (a < b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n < m))

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint16_dec_le"]
def UInt16.decLe (a b : UInt16) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n <= m))

instance (a b : UInt16) : Decidable (a < b) := UInt16.decLt a b
instance (a b : UInt16) : Decidable (a ≤ b) := UInt16.decLe a b
instance : Max UInt16 := maxOfLe
instance : Min UInt16 := minOfLe

@[extern "lean_uint32_of_nat"]
def UInt32.ofNat (n : @& Nat) : UInt32 := ⟨Fin.ofNat n⟩
@[extern "lean_uint32_of_nat"]
def UInt32.ofNat' (n : Nat) (h : n < UInt32.size) : UInt32 := ⟨⟨n, h⟩⟩
abbrev Nat.toUInt32 := UInt32.ofNat
@[extern "lean_uint32_add"]
def UInt32.add (a b : UInt32) : UInt32 := ⟨a.val + b.val⟩
@[extern "lean_uint32_sub"]
def UInt32.sub (a b : UInt32) : UInt32 := ⟨a.val - b.val⟩
@[extern "lean_uint32_mul"]
def UInt32.mul (a b : UInt32) : UInt32 := ⟨a.val * b.val⟩
@[extern "lean_uint32_div"]
def UInt32.div (a b : UInt32) : UInt32 := ⟨a.val / b.val⟩
@[extern "lean_uint32_mod"]
def UInt32.mod (a b : UInt32) : UInt32 := ⟨a.val % b.val⟩
@[extern "lean_uint32_modn"]
def UInt32.modn (a : UInt32) (n : @& Nat) : UInt32 := ⟨Fin.modn a.val n⟩
@[extern "lean_uint32_land"]
def UInt32.land (a b : UInt32) : UInt32 := ⟨Fin.land a.val b.val⟩
@[extern "lean_uint32_lor"]
def UInt32.lor (a b : UInt32) : UInt32 := ⟨Fin.lor a.val b.val⟩
@[extern "lean_uint32_xor"]
def UInt32.xor (a b : UInt32) : UInt32 := ⟨Fin.xor a.val b.val⟩
@[extern "lean_uint32_shift_left"]
def UInt32.shiftLeft (a b : UInt32) : UInt32 := ⟨a.val <<< (modn b 32).val⟩
@[extern "lean_uint32_shift_right"]
def UInt32.shiftRight (a b : UInt32) : UInt32 := ⟨a.val >>> (modn b 32).val⟩
@[extern "lean_uint32_to_uint8"]
def UInt32.toUInt8 (a : UInt32) : UInt8 := a.toNat.toUInt8
@[extern "lean_uint32_to_uint16"]
def UInt32.toUInt16 (a : UInt32) : UInt16 := a.toNat.toUInt16
@[extern "lean_uint8_to_uint32"]
def UInt8.toUInt32 (a : UInt8) : UInt32 := a.toNat.toUInt32
@[extern "lean_uint16_to_uint32"]
def UInt16.toUInt32 (a : UInt16) : UInt32 := a.toNat.toUInt32

instance : OfNat UInt32 n   := ⟨UInt32.ofNat n⟩
instance : Add UInt32       := ⟨UInt32.add⟩
instance : Sub UInt32       := ⟨UInt32.sub⟩
instance : Mul UInt32       := ⟨UInt32.mul⟩
instance : Mod UInt32       := ⟨UInt32.mod⟩
instance : HMod UInt32 Nat UInt32 := ⟨UInt32.modn⟩
instance : Div UInt32       := ⟨UInt32.div⟩

@[extern "lean_uint32_complement"]
def UInt32.complement (a:UInt32) : UInt32 := 0-(a+1)

instance : Complement UInt32 := ⟨UInt32.complement⟩
instance : AndOp UInt32     := ⟨UInt32.land⟩
instance : OrOp UInt32      := ⟨UInt32.lor⟩
instance : Xor UInt32       := ⟨UInt32.xor⟩
instance : ShiftLeft UInt32  := ⟨UInt32.shiftLeft⟩
instance : ShiftRight UInt32 := ⟨UInt32.shiftRight⟩

@[extern "lean_uint64_of_nat"]
def UInt64.ofNat (n : @& Nat) : UInt64 := ⟨Fin.ofNat n⟩
abbrev Nat.toUInt64 := UInt64.ofNat
@[extern "lean_uint64_to_nat"]
def UInt64.toNat (n : UInt64) : Nat := n.val.val
@[extern "lean_uint64_add"]
def UInt64.add (a b : UInt64) : UInt64 := ⟨a.val + b.val⟩
@[extern "lean_uint64_sub"]
def UInt64.sub (a b : UInt64) : UInt64 := ⟨a.val - b.val⟩
@[extern "lean_uint64_mul"]
def UInt64.mul (a b : UInt64) : UInt64 := ⟨a.val * b.val⟩
@[extern "lean_uint64_div"]
def UInt64.div (a b : UInt64) : UInt64 := ⟨a.val / b.val⟩
@[extern "lean_uint64_mod"]
def UInt64.mod (a b : UInt64) : UInt64 := ⟨a.val % b.val⟩
@[extern "lean_uint64_modn"]
def UInt64.modn (a : UInt64) (n : @& Nat) : UInt64 := ⟨Fin.modn a.val n⟩
@[extern "lean_uint64_land"]
def UInt64.land (a b : UInt64) : UInt64 := ⟨Fin.land a.val b.val⟩
@[extern "lean_uint64_lor"]
def UInt64.lor (a b : UInt64) : UInt64 := ⟨Fin.lor a.val b.val⟩
@[extern "lean_uint64_xor"]
def UInt64.xor (a b : UInt64) : UInt64 := ⟨Fin.xor a.val b.val⟩
@[extern "lean_uint64_shift_left"]
def UInt64.shiftLeft (a b : UInt64) : UInt64 := ⟨a.val <<< (modn b 64).val⟩
@[extern "lean_uint64_shift_right"]
def UInt64.shiftRight (a b : UInt64) : UInt64 := ⟨a.val >>> (modn b 64).val⟩
def UInt64.lt (a b : UInt64) : Prop := a.val < b.val
def UInt64.le (a b : UInt64) : Prop := a.val ≤ b.val
@[extern "lean_uint64_to_uint8"]
def UInt64.toUInt8 (a : UInt64) : UInt8 := a.toNat.toUInt8
@[extern "lean_uint64_to_uint16"]
def UInt64.toUInt16 (a : UInt64) : UInt16 := a.toNat.toUInt16
@[extern "lean_uint64_to_uint32"]
def UInt64.toUInt32 (a : UInt64) : UInt32 := a.toNat.toUInt32
@[extern "lean_uint8_to_uint64"]
def UInt8.toUInt64 (a : UInt8) : UInt64 := a.toNat.toUInt64
@[extern "lean_uint16_to_uint64"]
def UInt16.toUInt64 (a : UInt16) : UInt64 := a.toNat.toUInt64
@[extern "lean_uint32_to_uint64"]
def UInt32.toUInt64 (a : UInt32) : UInt64 := a.toNat.toUInt64

instance : OfNat UInt64 n   := ⟨UInt64.ofNat n⟩
instance : Add UInt64       := ⟨UInt64.add⟩
instance : Sub UInt64       := ⟨UInt64.sub⟩
instance : Mul UInt64       := ⟨UInt64.mul⟩
instance : Mod UInt64       := ⟨UInt64.mod⟩
instance : HMod UInt64 Nat UInt64 := ⟨UInt64.modn⟩
instance : Div UInt64       := ⟨UInt64.div⟩
instance : LT UInt64        := ⟨UInt64.lt⟩
instance : LE UInt64        := ⟨UInt64.le⟩

@[extern "lean_uint64_complement"]
def UInt64.complement (a:UInt64) : UInt64 := 0-(a+1)

instance : Complement UInt64 := ⟨UInt64.complement⟩
instance : AndOp UInt64     := ⟨UInt64.land⟩
instance : OrOp UInt64      := ⟨UInt64.lor⟩
instance : Xor UInt64       := ⟨UInt64.xor⟩
instance : ShiftLeft UInt64  := ⟨UInt64.shiftLeft⟩
instance : ShiftRight UInt64 := ⟨UInt64.shiftRight⟩

@[extern "lean_bool_to_uint64"]
def Bool.toUInt64 (b : Bool) : UInt64 := if b then 1 else 0

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint64_dec_lt"]
def UInt64.decLt (a b : UInt64) : Decidable (a < b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n < m))

set_option bootstrap.genMatcherCode false in
@[extern "lean_uint64_dec_le"]
def UInt64.decLe (a b : UInt64) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n <= m))

instance (a b : UInt64) : Decidable (a < b) := UInt64.decLt a b
instance (a b : UInt64) : Decidable (a ≤ b) := UInt64.decLe a b
instance : Max UInt64 := maxOfLe
instance : Min UInt64 := minOfLe

theorem usize_size_gt_zero : USize.size > 0 :=
  Nat.zero_lt_succ ..

@[extern "lean_usize_of_nat"]
def USize.ofNat (n : @& Nat) : USize := ⟨Fin.ofNat' n usize_size_gt_zero⟩
abbrev Nat.toUSize := USize.ofNat
@[extern "lean_usize_to_nat"]
def USize.toNat (n : USize) : Nat := n.val.val
@[extern "lean_usize_add"]
def USize.add (a b : USize) : USize := ⟨a.val + b.val⟩
@[extern "lean_usize_sub"]
def USize.sub (a b : USize) : USize := ⟨a.val - b.val⟩
@[extern "lean_usize_mul"]
def USize.mul (a b : USize) : USize := ⟨a.val * b.val⟩
@[extern "lean_usize_div"]
def USize.div (a b : USize) : USize := ⟨a.val / b.val⟩
@[extern "lean_usize_mod"]
def USize.mod (a b : USize) : USize := ⟨a.val % b.val⟩
@[extern "lean_usize_modn"]
def USize.modn (a : USize) (n : @& Nat) : USize := ⟨Fin.modn a.val n⟩
@[extern "lean_usize_land"]
def USize.land (a b : USize) : USize := ⟨Fin.land a.val b.val⟩
@[extern "lean_usize_lor"]
def USize.lor (a b : USize) : USize := ⟨Fin.lor a.val b.val⟩
@[extern "lean_usize_xor"]
def USize.xor (a b : USize) : USize := ⟨Fin.xor a.val b.val⟩
@[extern "lean_usize_shift_left"]
def USize.shiftLeft (a b : USize) : USize := ⟨a.val <<< (modn b System.Platform.numBits).val⟩
@[extern "lean_usize_shift_right"]
def USize.shiftRight (a b : USize) : USize := ⟨a.val >>> (modn b System.Platform.numBits).val⟩
@[extern "lean_uint32_to_usize"]
def UInt32.toUSize (a : UInt32) : USize := a.toNat.toUSize
@[extern "lean_usize_to_uint32"]
def USize.toUInt32 (a : USize) : UInt32 := a.toNat.toUInt32

def USize.lt (a b : USize) : Prop := a.val < b.val
def USize.le (a b : USize) : Prop := a.val ≤ b.val

instance : OfNat USize n   := ⟨USize.ofNat n⟩
instance : Add USize       := ⟨USize.add⟩
instance : Sub USize       := ⟨USize.sub⟩
instance : Mul USize       := ⟨USize.mul⟩
instance : Mod USize       := ⟨USize.mod⟩
instance : HMod USize Nat USize := ⟨USize.modn⟩
instance : Div USize       := ⟨USize.div⟩
instance : LT USize        := ⟨USize.lt⟩
instance : LE USize        := ⟨USize.le⟩

@[extern "lean_usize_complement"]
def USize.complement (a:USize) : USize := 0-(a+1)

instance : Complement USize := ⟨USize.complement⟩
instance : AndOp USize      := ⟨USize.land⟩
instance : OrOp USize       := ⟨USize.lor⟩
instance : Xor USize        := ⟨USize.xor⟩
instance : ShiftLeft USize  := ⟨USize.shiftLeft⟩
instance : ShiftRight USize := ⟨USize.shiftRight⟩

set_option bootstrap.genMatcherCode false in
@[extern "lean_usize_dec_lt"]
def USize.decLt (a b : USize) : Decidable (a < b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n < m))

set_option bootstrap.genMatcherCode false in
@[extern "lean_usize_dec_le"]
def USize.decLe (a b : USize) : Decidable (a ≤ b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ => inferInstanceAs (Decidable (n <= m))

instance (a b : USize) : Decidable (a < b) := USize.decLt a b
instance (a b : USize) : Decidable (a ≤ b) := USize.decLe a b
instance : Max USize := maxOfLe
instance : Min USize := minOfLe

theorem USize.modn_lt {m : Nat} : ∀ (u : USize), m > 0 → USize.toNat (u % m) < m
  | ⟨u⟩, h => Fin.modn_lt u h
