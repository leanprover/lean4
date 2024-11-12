/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.UInt.Basic

/-!
This module contains the definition of signed fixed width integer types as well as basic arithmetic
and bitwise operations on top of it.
-/


/--
The type of signed 8-bit integers. This type has special support in the
compiler to make it actually 8 bits rather than wrapping a `Nat`.
-/
structure Int8 where
  /--
  Obtain the `UInt8` that is 2's complement equivalent to the `Int8`.
  -/
  toUInt8 : UInt8

/--
The type of signed 16-bit integers. This type has special support in the
compiler to make it actually 16 bits rather than wrapping a `Nat`.
-/
structure Int16 where
  /--
  Obtain the `UInt16` that is 2's complement equivalent to the `Int16`.
  -/
  toUInt16 : UInt16

/--
The type of signed 32-bit integers. This type has special support in the
compiler to make it actually 32 bits rather than wrapping a `Nat`.
-/
structure Int32 where
  /--
  Obtain the `UInt32` that is 2's complement equivalent to the `Int32`.
  -/
  toUInt32 : UInt32

/--
The type of signed 64-bit integers. This type has special support in the
compiler to make it actually 64 bits rather than wrapping a `Nat`.
-/
structure Int64 where
  /--
  Obtain the `UInt64` that is 2's complement equivalent to the `Int64`.
  -/
  toUInt64 : UInt64

/--
A `ISize` is a signed integer with the size of a word for the platform's architecture.

For example, if running on a 32-bit machine, ISize is equivalent to `Int32`.
Or on a 64-bit machine, `Int64`.
-/
structure ISize where
  /--
  Obtain the `USize` that is 2's complement equivalent to the `ISize`.
  -/
  toUSize : USize

/-- The size of type `Int8`, that is, `2^8 = 256`. -/
abbrev Int8.size : Nat := 256

/--
Obtain the `BitVec` that contains the 2's complement representation of the `Int8`.
-/
@[inline] def Int8.toBitVec (x : Int8) : BitVec 8 := x.toUInt8.toBitVec

@[extern "lean_int8_of_int"]
def Int8.ofInt (i : @& Int) : Int8 := ⟨⟨BitVec.ofInt 8 i⟩⟩
@[extern "lean_int8_of_nat"]
def Int8.ofNat (n : @& Nat) : Int8 := ⟨⟨BitVec.ofNat 8 n⟩⟩
abbrev Int.toInt8 := Int8.ofInt
abbrev Nat.toInt8 := Int8.ofNat
@[extern "lean_int8_to_int"]
def Int8.toInt (i : Int8) : Int := i.toBitVec.toInt
/--
This function has the same behavior as `Int.toNat` for negative numbers.
If you want to obtain the 2's complement representation use `toBitVec`.
-/
@[inline] def Int8.toNat (i : Int8) : Nat := i.toInt.toNat
@[extern "lean_int8_neg"]
def Int8.neg (i : Int8) : Int8 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int8 where
  toString i := toString i.toInt

instance : OfNat Int8 n := ⟨Int8.ofNat n⟩
instance : Neg Int8 where
  neg := Int8.neg

@[extern "lean_int8_add"]
def Int8.add (a b : Int8) : Int8 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
@[extern "lean_int8_sub"]
def Int8.sub (a b : Int8) : Int8 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
@[extern "lean_int8_mul"]
def Int8.mul (a b : Int8) : Int8 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
@[extern "lean_int8_div"]
def Int8.div (a b : Int8) : Int8 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
@[extern "lean_int8_mod"]
def Int8.mod (a b : Int8) : Int8 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
@[extern "lean_int8_land"]
def Int8.land (a b : Int8) : Int8 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
@[extern "lean_int8_lor"]
def Int8.lor (a b : Int8) : Int8 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
@[extern "lean_int8_xor"]
def Int8.xor (a b : Int8) : Int8 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
@[extern "lean_int8_shift_left"]
def Int8.shiftLeft (a b : Int8) : Int8 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 8)⟩⟩
@[extern "lean_int8_shift_right"]
def Int8.shiftRight (a b : Int8) : Int8 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 8)⟩⟩
@[extern "lean_int8_complement"]
def Int8.complement (a : Int8) : Int8 := ⟨⟨~~~a.toBitVec⟩⟩

@[extern "lean_int8_dec_eq"]
def Int8.decEq (a b : Int8) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int8.noConfusion h' (fun h' => absurd h' h))

def Int8.lt (a b : Int8) : Prop := a.toBitVec.slt b.toBitVec
def Int8.le (a b : Int8) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int8 where
  default := 0

instance : Add Int8         := ⟨Int8.add⟩
instance : Sub Int8         := ⟨Int8.sub⟩
instance : Mul Int8         := ⟨Int8.mul⟩
instance : Mod Int8         := ⟨Int8.mod⟩
instance : Div Int8         := ⟨Int8.div⟩
instance : LT Int8          := ⟨Int8.lt⟩
instance : LE Int8          := ⟨Int8.le⟩
instance : Complement Int8  := ⟨Int8.complement⟩
instance : AndOp Int8       := ⟨Int8.land⟩
instance : OrOp Int8        := ⟨Int8.lor⟩
instance : Xor Int8         := ⟨Int8.xor⟩
instance : ShiftLeft Int8   := ⟨Int8.shiftLeft⟩
instance : ShiftRight Int8  := ⟨Int8.shiftRight⟩
instance : DecidableEq Int8 := Int8.decEq

@[extern "lean_int8_dec_lt"]
def Int8.decLt (a b : Int8) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

@[extern "lean_int8_dec_le"]
def Int8.decLe (a b : Int8) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : Int8) : Decidable (a < b) := Int8.decLt a b
instance (a b : Int8) : Decidable (a ≤ b) := Int8.decLe a b
instance : Max Int8 := maxOfLe
instance : Min Int8 := minOfLe

/-- The size of type `Int16`, that is, `2^16 = 65536`. -/
abbrev Int16.size : Nat := 65536

/--
Obtain the `BitVec` that contains the 2's complement representation of the `Int16`.
-/
@[inline] def Int16.toBitVec (x : Int16) : BitVec 16 := x.toUInt16.toBitVec

@[extern "lean_int16_of_int"]
def Int16.ofInt (i : @& Int) : Int16 := ⟨⟨BitVec.ofInt 16 i⟩⟩
@[extern "lean_int16_of_nat"]
def Int16.ofNat (n : @& Nat) : Int16 := ⟨⟨BitVec.ofNat 16 n⟩⟩
abbrev Int.toInt16 := Int16.ofInt
abbrev Nat.toInt16 := Int16.ofNat
@[extern "lean_int16_to_int"]
def Int16.toInt (i : Int16) : Int := i.toBitVec.toInt
/--
This function has the same behavior as `Int.toNat` for negative numbers.
If you want to obtain the 2's complement representation use `toBitVec`.
-/
@[inline] def Int16.toNat (i : Int16) : Nat := i.toInt.toNat
@[extern "lean_int16_to_int8"]
def Int16.toInt8 (a : Int16) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
@[extern "lean_int8_to_int16"]
def Int8.toInt16 (a : Int8) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
@[extern "lean_int16_neg"]
def Int16.neg (i : Int16) : Int16 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int16 where
  toString i := toString i.toInt

instance : OfNat Int16 n := ⟨Int16.ofNat n⟩
instance : Neg Int16 where
  neg := Int16.neg

@[extern "lean_int16_add"]
def Int16.add (a b : Int16) : Int16 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
@[extern "lean_int16_sub"]
def Int16.sub (a b : Int16) : Int16 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
@[extern "lean_int16_mul"]
def Int16.mul (a b : Int16) : Int16 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
@[extern "lean_int16_div"]
def Int16.div (a b : Int16) : Int16 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
@[extern "lean_int16_mod"]
def Int16.mod (a b : Int16) : Int16 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
@[extern "lean_int16_land"]
def Int16.land (a b : Int16) : Int16 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
@[extern "lean_int16_lor"]
def Int16.lor (a b : Int16) : Int16 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
@[extern "lean_int16_xor"]
def Int16.xor (a b : Int16) : Int16 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
@[extern "lean_int16_shift_left"]
def Int16.shiftLeft (a b : Int16) : Int16 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 16)⟩⟩
@[extern "lean_int16_shift_right"]
def Int16.shiftRight (a b : Int16) : Int16 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 16)⟩⟩
@[extern "lean_int16_complement"]
def Int16.complement (a : Int16) : Int16 := ⟨⟨~~~a.toBitVec⟩⟩

@[extern "lean_int16_dec_eq"]
def Int16.decEq (a b : Int16) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int16.noConfusion h' (fun h' => absurd h' h))

def Int16.lt (a b : Int16) : Prop := a.toBitVec.slt b.toBitVec
def Int16.le (a b : Int16) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int16 where
  default := 0

instance : Add Int16         := ⟨Int16.add⟩
instance : Sub Int16         := ⟨Int16.sub⟩
instance : Mul Int16         := ⟨Int16.mul⟩
instance : Mod Int16         := ⟨Int16.mod⟩
instance : Div Int16         := ⟨Int16.div⟩
instance : LT Int16          := ⟨Int16.lt⟩
instance : LE Int16          := ⟨Int16.le⟩
instance : Complement Int16  := ⟨Int16.complement⟩
instance : AndOp Int16       := ⟨Int16.land⟩
instance : OrOp Int16        := ⟨Int16.lor⟩
instance : Xor Int16         := ⟨Int16.xor⟩
instance : ShiftLeft Int16   := ⟨Int16.shiftLeft⟩
instance : ShiftRight Int16  := ⟨Int16.shiftRight⟩
instance : DecidableEq Int16 := Int16.decEq

@[extern "lean_int16_dec_lt"]
def Int16.decLt (a b : Int16) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

@[extern "lean_int16_dec_le"]
def Int16.decLe (a b : Int16) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : Int16) : Decidable (a < b) := Int16.decLt a b
instance (a b : Int16) : Decidable (a ≤ b) := Int16.decLe a b
instance : Max Int16 := maxOfLe
instance : Min Int16 := minOfLe

/-- The size of type `Int32`, that is, `2^32 = 4294967296`. -/
abbrev Int32.size : Nat := 4294967296

/--
Obtain the `BitVec` that contains the 2's complement representation of the `Int32`.
-/
@[inline] def Int32.toBitVec (x : Int32) : BitVec 32 := x.toUInt32.toBitVec

@[extern "lean_int32_of_int"]
def Int32.ofInt (i : @& Int) : Int32 := ⟨⟨BitVec.ofInt 32 i⟩⟩
@[extern "lean_int32_of_nat"]
def Int32.ofNat (n : @& Nat) : Int32 := ⟨⟨BitVec.ofNat 32 n⟩⟩
abbrev Int.toInt32 := Int32.ofInt
abbrev Nat.toInt32 := Int32.ofNat
@[extern "lean_int32_to_int"]
def Int32.toInt (i : Int32) : Int := i.toBitVec.toInt
/--
This function has the same behavior as `Int.toNat` for negative numbers.
If you want to obtain the 2's complement representation use `toBitVec`.
-/
@[inline] def Int32.toNat (i : Int32) : Nat := i.toInt.toNat
@[extern "lean_int32_to_int8"]
def Int32.toInt8 (a : Int32) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
@[extern "lean_int32_to_int16"]
def Int32.toInt16 (a : Int32) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
@[extern "lean_int8_to_int32"]
def Int8.toInt32 (a : Int8) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
@[extern "lean_int16_to_int32"]
def Int16.toInt32 (a : Int16) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
@[extern "lean_int32_neg"]
def Int32.neg (i : Int32) : Int32 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int32 where
  toString i := toString i.toInt

instance : OfNat Int32 n := ⟨Int32.ofNat n⟩
instance : Neg Int32 where
  neg := Int32.neg

@[extern "lean_int32_add"]
def Int32.add (a b : Int32) : Int32 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
@[extern "lean_int32_sub"]
def Int32.sub (a b : Int32) : Int32 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
@[extern "lean_int32_mul"]
def Int32.mul (a b : Int32) : Int32 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
@[extern "lean_int32_div"]
def Int32.div (a b : Int32) : Int32 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
@[extern "lean_int32_mod"]
def Int32.mod (a b : Int32) : Int32 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
@[extern "lean_int32_land"]
def Int32.land (a b : Int32) : Int32 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
@[extern "lean_int32_lor"]
def Int32.lor (a b : Int32) : Int32 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
@[extern "lean_int32_xor"]
def Int32.xor (a b : Int32) : Int32 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
@[extern "lean_int32_shift_left"]
def Int32.shiftLeft (a b : Int32) : Int32 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 32)⟩⟩
@[extern "lean_int32_shift_right"]
def Int32.shiftRight (a b : Int32) : Int32 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 32)⟩⟩
@[extern "lean_int32_complement"]
def Int32.complement (a : Int32) : Int32 := ⟨⟨~~~a.toBitVec⟩⟩

@[extern "lean_int32_dec_eq"]
def Int32.decEq (a b : Int32) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int32.noConfusion h' (fun h' => absurd h' h))

def Int32.lt (a b : Int32) : Prop := a.toBitVec.slt b.toBitVec
def Int32.le (a b : Int32) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int32 where
  default := 0

instance : Add Int32         := ⟨Int32.add⟩
instance : Sub Int32         := ⟨Int32.sub⟩
instance : Mul Int32         := ⟨Int32.mul⟩
instance : Mod Int32         := ⟨Int32.mod⟩
instance : Div Int32         := ⟨Int32.div⟩
instance : LT Int32          := ⟨Int32.lt⟩
instance : LE Int32          := ⟨Int32.le⟩
instance : Complement Int32  := ⟨Int32.complement⟩
instance : AndOp Int32       := ⟨Int32.land⟩
instance : OrOp Int32        := ⟨Int32.lor⟩
instance : Xor Int32         := ⟨Int32.xor⟩
instance : ShiftLeft Int32   := ⟨Int32.shiftLeft⟩
instance : ShiftRight Int32  := ⟨Int32.shiftRight⟩
instance : DecidableEq Int32 := Int32.decEq

@[extern "lean_int32_dec_lt"]
def Int32.decLt (a b : Int32) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

@[extern "lean_int32_dec_le"]
def Int32.decLe (a b : Int32) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : Int32) : Decidable (a < b) := Int32.decLt a b
instance (a b : Int32) : Decidable (a ≤ b) := Int32.decLe a b
instance : Max Int32 := maxOfLe
instance : Min Int32 := minOfLe

/-- The size of type `Int64`, that is, `2^64 = 18446744073709551616`. -/
abbrev Int64.size : Nat := 18446744073709551616

/--
Obtain the `BitVec` that contains the 2's complement representation of the `Int64`.
-/
@[inline] def Int64.toBitVec (x : Int64) : BitVec 64 := x.toUInt64.toBitVec

@[extern "lean_int64_of_int"]
def Int64.ofInt (i : @& Int) : Int64 := ⟨⟨BitVec.ofInt 64 i⟩⟩
@[extern "lean_int64_of_nat"]
def Int64.ofNat (n : @& Nat) : Int64 := ⟨⟨BitVec.ofNat 64 n⟩⟩
abbrev Int.toInt64 := Int64.ofInt
abbrev Nat.toInt64 := Int64.ofNat
@[extern "lean_int64_to_int_sint"]
def Int64.toInt (i : Int64) : Int := i.toBitVec.toInt
/--
This function has the same behavior as `Int.toNat` for negative numbers.
If you want to obtain the 2's complement representation use `toBitVec`.
-/
@[inline] def Int64.toNat (i : Int64) : Nat := i.toInt.toNat
@[extern "lean_int64_to_int8"]
def Int64.toInt8 (a : Int64) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
@[extern "lean_int64_to_int16"]
def Int64.toInt16 (a : Int64) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
@[extern "lean_int64_to_int32"]
def Int64.toInt32 (a : Int64) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
@[extern "lean_int8_to_int64"]
def Int8.toInt64 (a : Int8) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
@[extern "lean_int16_to_int64"]
def Int16.toInt64 (a : Int16) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
@[extern "lean_int32_to_int64"]
def Int32.toInt64 (a : Int32) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
@[extern "lean_int64_neg"]
def Int64.neg (i : Int64) : Int64 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int64 where
  toString i := toString i.toInt

instance : OfNat Int64 n := ⟨Int64.ofNat n⟩
instance : Neg Int64 where
  neg := Int64.neg

@[extern "lean_int64_add"]
def Int64.add (a b : Int64) : Int64 := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
@[extern "lean_int64_sub"]
def Int64.sub (a b : Int64) : Int64 := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
@[extern "lean_int64_mul"]
def Int64.mul (a b : Int64) : Int64 := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
@[extern "lean_int64_div"]
def Int64.div (a b : Int64) : Int64 := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
@[extern "lean_int64_mod"]
def Int64.mod (a b : Int64) : Int64 := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
@[extern "lean_int64_land"]
def Int64.land (a b : Int64) : Int64 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
@[extern "lean_int64_lor"]
def Int64.lor (a b : Int64) : Int64 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
@[extern "lean_int64_xor"]
def Int64.xor (a b : Int64) : Int64 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
@[extern "lean_int64_shift_left"]
def Int64.shiftLeft (a b : Int64) : Int64 := ⟨⟨a.toBitVec <<< (b.toBitVec.smod 64)⟩⟩
@[extern "lean_int64_shift_right"]
def Int64.shiftRight (a b : Int64) : Int64 := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod 64)⟩⟩
@[extern "lean_int64_complement"]
def Int64.complement (a : Int64) : Int64 := ⟨⟨~~~a.toBitVec⟩⟩

@[extern "lean_int64_dec_eq"]
def Int64.decEq (a b : Int64) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => Int64.noConfusion h' (fun h' => absurd h' h))

def Int64.lt (a b : Int64) : Prop := a.toBitVec.slt b.toBitVec
def Int64.le (a b : Int64) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited Int64 where
  default := 0

instance : Add Int64         := ⟨Int64.add⟩
instance : Sub Int64         := ⟨Int64.sub⟩
instance : Mul Int64         := ⟨Int64.mul⟩
instance : Mod Int64         := ⟨Int64.mod⟩
instance : Div Int64         := ⟨Int64.div⟩
instance : LT Int64          := ⟨Int64.lt⟩
instance : LE Int64          := ⟨Int64.le⟩
instance : Complement Int64  := ⟨Int64.complement⟩
instance : AndOp Int64       := ⟨Int64.land⟩
instance : OrOp Int64        := ⟨Int64.lor⟩
instance : Xor Int64         := ⟨Int64.xor⟩
instance : ShiftLeft Int64   := ⟨Int64.shiftLeft⟩
instance : ShiftRight Int64  := ⟨Int64.shiftRight⟩
instance : DecidableEq Int64 := Int64.decEq

@[extern "lean_int64_dec_lt"]
def Int64.decLt (a b : Int64) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

@[extern "lean_int64_dec_le"]
def Int64.decLe (a b : Int64) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : Int64) : Decidable (a < b) := Int64.decLt a b
instance (a b : Int64) : Decidable (a ≤ b) := Int64.decLe a b
instance : Max Int64 := maxOfLe
instance : Min Int64 := minOfLe

/-- The size of type `ISize`, that is, `2^System.Platform.numBits`. -/
abbrev ISize.size : Nat := 2^System.Platform.numBits

/--
Obtain the `BitVec` that contains the 2's complement representation of the `ISize`.
-/
@[inline] def ISize.toBitVec (x : ISize) : BitVec System.Platform.numBits := x.toUSize.toBitVec

@[extern "lean_isize_of_int"]
def ISize.ofInt (i : @& Int) : ISize := ⟨⟨BitVec.ofInt System.Platform.numBits i⟩⟩
@[extern "lean_isize_of_nat"]
def ISize.ofNat (n : @& Nat) : ISize := ⟨⟨BitVec.ofNat System.Platform.numBits n⟩⟩
abbrev Int.toISize := ISize.ofInt
abbrev Nat.toISize := ISize.ofNat
@[extern "lean_isize_to_int"]
def ISize.toInt (i : ISize) : Int := i.toBitVec.toInt
/--
This function has the same behavior as `Int.toNat` for negative numbers.
If you want to obtain the 2's complement representation use `toBitVec`.
-/
@[inline] def ISize.toNat (i : ISize) : Nat := i.toInt.toNat
@[extern "lean_isize_to_int32"]
def ISize.toInt32 (a : ISize) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
/--
Upcast `ISize` to `Int64`. This function is losless as `ISize` is either `Int32` or `Int64`.
-/
@[extern "lean_isize_to_int64"]
def ISize.toInt64 (a : ISize) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
/--
Upcast `Int32` to `ISize`. This function is losless as `ISize` is either `Int32` or `Int64`.
-/
@[extern "lean_int32_to_isize"]
def Int32.toISize (a : Int32) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
@[extern "lean_int64_to_isize"]
def Int64.toISize (a : Int64) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
@[extern "lean_isize_neg"]
def ISize.neg (i : ISize) : ISize := ⟨⟨-i.toBitVec⟩⟩

instance : ToString ISize where
  toString i := toString i.toInt

instance : OfNat ISize n := ⟨ISize.ofNat n⟩
instance : Neg ISize where
  neg := ISize.neg

@[extern "lean_isize_add"]
def ISize.add (a b : ISize) : ISize := ⟨⟨a.toBitVec + b.toBitVec⟩⟩
@[extern "lean_isize_sub"]
def ISize.sub (a b : ISize) : ISize := ⟨⟨a.toBitVec - b.toBitVec⟩⟩
@[extern "lean_isize_mul"]
def ISize.mul (a b : ISize) : ISize := ⟨⟨a.toBitVec * b.toBitVec⟩⟩
@[extern "lean_isize_div"]
def ISize.div (a b : ISize) : ISize := ⟨⟨BitVec.sdiv a.toBitVec b.toBitVec⟩⟩
@[extern "lean_isize_mod"]
def ISize.mod (a b : ISize) : ISize := ⟨⟨BitVec.srem a.toBitVec b.toBitVec⟩⟩
@[extern "lean_isize_land"]
def ISize.land (a b : ISize) : ISize := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
@[extern "lean_isize_lor"]
def ISize.lor (a b : ISize) : ISize := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
@[extern "lean_isize_xor"]
def ISize.xor (a b : ISize) : ISize := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
@[extern "lean_isize_shift_left"]
def ISize.shiftLeft (a b : ISize) : ISize := ⟨⟨a.toBitVec <<< (b.toBitVec.smod System.Platform.numBits)⟩⟩
@[extern "lean_isize_shift_right"]
def ISize.shiftRight (a b : ISize) : ISize := ⟨⟨BitVec.sshiftRight' a.toBitVec (b.toBitVec.smod System.Platform.numBits)⟩⟩
@[extern "lean_isize_complement"]
def ISize.complement (a : ISize) : ISize := ⟨⟨~~~a.toBitVec⟩⟩

@[extern "lean_isize_dec_eq"]
def ISize.decEq (a b : ISize) : Decidable (a = b) :=
  match a, b with
  | ⟨n⟩, ⟨m⟩ =>
    if h : n = m then
      isTrue <| h ▸ rfl
    else
      isFalse (fun h' => ISize.noConfusion h' (fun h' => absurd h' h))

def ISize.lt (a b : ISize) : Prop := a.toBitVec.slt b.toBitVec
def ISize.le (a b : ISize) : Prop := a.toBitVec.sle b.toBitVec

instance : Inhabited ISize where
  default := 0

instance : Add ISize         := ⟨ISize.add⟩
instance : Sub ISize         := ⟨ISize.sub⟩
instance : Mul ISize         := ⟨ISize.mul⟩
instance : Mod ISize         := ⟨ISize.mod⟩
instance : Div ISize         := ⟨ISize.div⟩
instance : LT ISize          := ⟨ISize.lt⟩
instance : LE ISize          := ⟨ISize.le⟩
instance : Complement ISize  := ⟨ISize.complement⟩
instance : AndOp ISize       := ⟨ISize.land⟩
instance : OrOp ISize        := ⟨ISize.lor⟩
instance : Xor ISize         := ⟨ISize.xor⟩
instance : ShiftLeft ISize   := ⟨ISize.shiftLeft⟩
instance : ShiftRight ISize  := ⟨ISize.shiftRight⟩
instance : DecidableEq ISize := ISize.decEq

@[extern "lean_isize_dec_lt"]
def ISize.decLt (a b : ISize) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec.slt b.toBitVec))

@[extern "lean_isize_dec_le"]
def ISize.decLe (a b : ISize) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec.sle b.toBitVec))

instance (a b : ISize) : Decidable (a < b) := ISize.decLt a b
instance (a b : ISize) : Decidable (a ≤ b) := ISize.decLe a b
instance : Max ISize := maxOfLe
instance : Min ISize := minOfLe
