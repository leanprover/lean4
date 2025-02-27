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
  private ofUInt8 ::
  /--
  Obtain the `UInt8` that is 2's complement equivalent to the `Int8`.
  -/
  toUInt8 : UInt8

/--
The type of signed 16-bit integers. This type has special support in the
compiler to make it actually 16 bits rather than wrapping a `Nat`.
-/
structure Int16 where
  private ofUInt16 ::
  /--
  Obtain the `UInt16` that is 2's complement equivalent to the `Int16`.
  -/
  toUInt16 : UInt16

/--
The type of signed 32-bit integers. This type has special support in the
compiler to make it actually 32 bits rather than wrapping a `Nat`.
-/
structure Int32 where
  private ofUInt32 ::
  /--
  Obtain the `UInt32` that is 2's complement equivalent to the `Int32`.
  -/
  toUInt32 : UInt32

/--
The type of signed 64-bit integers. This type has special support in the
compiler to make it actually 64 bits rather than wrapping a `Nat`.
-/
structure Int64 where
  private ofUInt64 ::
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
  private ofUSize ::
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

theorem Int8.toBitVec.inj : {x y : Int8} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `Int8` that is 2's complement equivalent to the `UInt8`. -/
@[inline] def UInt8.toInt8 (i : UInt8) : Int8 := Int8.ofUInt8 i
@[inline, deprecated UInt8.toInt8 (since := "2025-02-13"), inherit_doc UInt8.toInt8]
def Int8.mk (i : UInt8) : Int8 := UInt8.toInt8 i
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
@[inline] def Int8.toNatClampNeg (i : Int8) : Nat := i.toInt.toNat
@[inline, deprecated Int8.toNatClampNeg (since := "2025-02-13"), inherit_doc Int8.toNatClampNeg]
def Int8.toNat (i : Int8) : Nat := i.toInt.toNat
/-- Obtains the `Int8` whose 2's complement representation is the given `BitVec 8`. -/
@[inline] def Int8.ofBitVec (b : BitVec 8) : Int8 := ⟨⟨b⟩⟩
@[extern "lean_int8_neg"]
def Int8.neg (i : Int8) : Int8 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int8 where
  toString i := toString i.toInt
instance : Repr Int8 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom Int8 := ⟨⟩

instance : Hashable Int8 where
  hash i := i.toUInt8.toUInt64

instance Int8.instOfNat : OfNat Int8 n := ⟨Int8.ofNat n⟩
instance Int8.instNeg : Neg Int8 where
  neg := Int8.neg

/-- The maximum value an `Int8` may attain, that is, `2^7 - 1 = 127`. -/
abbrev Int8.maxValue : Int8 := 127
/-- The minimum value an `Int8` may attain, that is, `-2^7 = -128`. -/
abbrev Int8.minValue : Int8 := -128
/-- Constructs an `Int8` from an `Int` which is known to be in bounds. -/
@[inline]
def Int8.ofIntLE (i : Int) (_hl : Int8.minValue.toInt ≤ i) (_hr : i ≤ Int8.maxValue.toInt) : Int8 :=
  Int8.ofInt i
/-- Constructs an `Int8` from an `Int`, clamping if the value is too small or too large. -/
def Int8.ofIntTruncate (i : Int) : Int8 :=
  if hl : Int8.minValue.toInt ≤ i then
    if hr : i ≤ Int8.maxValue.toInt then
      Int8.ofIntLE i hl hr
    else
      Int8.minValue
  else
    Int8.minValue

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
/-- Computes the absolute value of the signed integer. This function is equivalent to
`if a < 0 then -a else a`, so in particular `Int8.minValue` will be mapped to `Int8.minValue`. -/
@[extern "lean_int8_abs"]
def Int8.abs (a : Int8) : Int8 := ⟨⟨a.toBitVec.abs⟩⟩

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

@[extern "lean_bool_to_int8"]
def Bool.toInt8 (b : Bool) : Int8 := if b then 1 else 0

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

theorem Int16.toBitVec.inj : {x y : Int16} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `Int16` that is 2's complement equivalent to the `UInt16`. -/
@[inline] def UInt16.toInt16 (i : UInt16) : Int16 := Int16.ofUInt16 i
@[inline, deprecated UInt16.toInt16 (since := "2025-02-13"), inherit_doc UInt16.toInt16]
def Int16.mk (i : UInt16) : Int16 := UInt16.toInt16 i
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
@[inline] def Int16.toNatClampNeg (i : Int16) : Nat := i.toInt.toNat
@[inline, deprecated Int16.toNatClampNeg (since := "2025-02-13"), inherit_doc Int16.toNatClampNeg]
def Int16.toNat (i : Int16) : Nat := i.toInt.toNat
/-- Obtains the `Int16` whose 2's complement representation is the given `BitVec 16`. -/
@[inline] def Int16.ofBitVec (b : BitVec 16) : Int16 := ⟨⟨b⟩⟩
@[extern "lean_int16_to_int8"]
def Int16.toInt8 (a : Int16) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
@[extern "lean_int8_to_int16"]
def Int8.toInt16 (a : Int8) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
@[extern "lean_int16_neg"]
def Int16.neg (i : Int16) : Int16 := ⟨⟨-i.toBitVec⟩⟩

instance : ToString Int16 where
  toString i := toString i.toInt
instance : Repr Int16 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom Int16 := ⟨⟩

instance : Hashable Int16 where
  hash i := i.toUInt16.toUInt64

instance Int16.instOfNat : OfNat Int16 n := ⟨Int16.ofNat n⟩
instance Int16.instNeg : Neg Int16 where
  neg := Int16.neg

/-- The maximum value an `Int16` may attain, that is, `2^15 - 1 = 32767`. -/
abbrev Int16.maxValue : Int16 := 32767
/-- The minimum value an `Int16` may attain, that is, `-2^15 = -32768`. -/
abbrev Int16.minValue : Int16 := -32768
/-- Constructs an `Int16` from an `Int` which is known to be in bounds. -/
@[inline]
def Int16.ofIntLE (i : Int) (_hl : Int16.minValue.toInt ≤ i) (_hr : i ≤ Int16.maxValue.toInt) : Int16 :=
  Int16.ofInt i
/-- Constructs an `Int16` from an `Int`, clamping if the value is too small or too large. -/
def Int16.ofIntTruncate (i : Int) : Int16 :=
  if hl : Int16.minValue.toInt ≤ i then
    if hr : i ≤ Int16.maxValue.toInt then
      Int16.ofIntLE i hl hr
    else
      Int16.minValue
  else
    Int16.minValue

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
/-- Computes the absolute value of the signed integer. This function is equivalent to
`if a < 0 then -a else a`, so in particular `Int16.minValue` will be mapped to `Int16.minValue`. -/
@[extern "lean_int16_abs"]
def Int16.abs (a : Int16) : Int16 := ⟨⟨a.toBitVec.abs⟩⟩

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

@[extern "lean_bool_to_int16"]
def Bool.toInt16 (b : Bool) : Int16 := if b then 1 else 0

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

theorem Int32.toBitVec.inj : {x y : Int32} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `Int32` that is 2's complement equivalent to the `UInt32`. -/
@[inline] def UInt32.toInt32 (i : UInt32) : Int32 := Int32.ofUInt32 i
@[inline, deprecated UInt32.toInt32 (since := "2025-02-13"), inherit_doc UInt32.toInt32]
def Int32.mk (i : UInt32) : Int32 := UInt32.toInt32 i
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
@[inline] def Int32.toNatClampNeg (i : Int32) : Nat := i.toInt.toNat
@[inline, deprecated Int32.toNatClampNeg (since := "2025-02-13"), inherit_doc Int32.toNatClampNeg]
def Int32.toNat (i : Int32) : Nat := i.toInt.toNat
/-- Obtains the `Int32` whose 2's complement representation is the given `BitVec 32`. -/
@[inline] def Int32.ofBitVec (b : BitVec 32) : Int32 := ⟨⟨b⟩⟩
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
instance : Repr Int16 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom Int16 := ⟨⟩

instance : Hashable Int32 where
  hash i := i.toUInt32.toUInt64

instance Int32.instOfNat : OfNat Int32 n := ⟨Int32.ofNat n⟩
instance Int32.instNeg : Neg Int32 where
  neg := Int32.neg

/-- The maximum value an `Int32` may attain, that is, `2^31 - 1 = 2147483647`. -/
abbrev Int32.maxValue : Int32 := 2147483647
/-- The minimum value an `Int32` may attain, that is, `-2^31 = -2147483648`. -/
abbrev Int32.minValue : Int32 := -2147483648
/-- Constructs an `Int32` from an `Int` which is known to be in bounds. -/
@[inline]
def Int32.ofIntLE (i : Int) (_hl : Int32.minValue.toInt ≤ i) (_hr : i ≤ Int32.maxValue.toInt) : Int32 :=
  Int32.ofInt i
/-- Constructs an `Int32` from an `Int`, clamping if the value is too small or too large. -/
def Int32.ofIntTruncate (i : Int) : Int32 :=
  if hl : Int32.minValue.toInt ≤ i then
    if hr : i ≤ Int32.maxValue.toInt then
      Int32.ofIntLE i hl hr
    else
      Int32.minValue
  else
    Int32.minValue

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
/-- Computes the absolute value of the signed integer. This function is equivalent to
`if a < 0 then -a else a`, so in particular `Int32.minValue` will be mapped to `Int32.minValue`. -/
@[extern "lean_int32_abs"]
def Int32.abs (a : Int32) : Int32 := ⟨⟨a.toBitVec.abs⟩⟩

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

@[extern "lean_bool_to_int32"]
def Bool.toInt32 (b : Bool) : Int32 := if b then 1 else 0

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

theorem Int64.toBitVec.inj : {x y : Int64} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `Int64` that is 2's complement equivalent to the `UInt64`. -/
@[inline] def UInt64.toInt64 (i : UInt64) : Int64 := Int64.ofUInt64 i
@[inline, deprecated UInt64.toInt64 (since := "2025-02-13"), inherit_doc UInt64.toInt64]
def Int64.mk (i : UInt64) : Int64 := UInt64.toInt64 i
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
@[inline] def Int64.toNatClampNeg (i : Int64) : Nat := i.toInt.toNat
@[inline, deprecated Int64.toNatClampNeg (since := "2025-02-13"), inherit_doc Int64.toNatClampNeg]
def Int64.toNat (i : Int64) : Nat := i.toInt.toNat
/-- Obtains the `Int64` whose 2's complement representation is the given `BitVec 64`. -/
@[inline] def Int64.ofBitVec (b : BitVec 64) : Int64 := ⟨⟨b⟩⟩
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
instance : Repr Int64 where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom Int64 := ⟨⟩

instance : Hashable Int64 where
  hash i := i.toUInt64

instance Int64.instOfNat : OfNat Int64 n := ⟨Int64.ofNat n⟩
instance Int64.instNeg : Neg Int64 where
  neg := Int64.neg

/-- The maximum value an `Int64` may attain, that is, `2^63 - 1 = 9223372036854775807`. -/
abbrev Int64.maxValue : Int64 := 9223372036854775807
/-- The minimum value an `Int64` may attain, that is, `-2^63 = -9223372036854775808`. -/
abbrev Int64.minValue : Int64 := -9223372036854775808
/-- Constructs an `Int64` from an `Int` which is known to be in bounds. -/
@[inline]
def Int64.ofIntLE (i : Int) (_hl : Int64.minValue.toInt ≤ i) (_hr : i ≤ Int64.maxValue.toInt) : Int64 :=
  Int64.ofInt i
/-- Constructs an `Int64` from an `Int`, clamping if the value is too small or too large. -/
def Int64.ofIntTruncate (i : Int) : Int64 :=
  if hl : Int64.minValue.toInt ≤ i then
    if hr : i ≤ Int64.maxValue.toInt then
      Int64.ofIntLE i hl hr
    else
      Int64.minValue
  else
    Int64.minValue

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
/-- Computes the absolute value of the signed integer. This function is equivalent to
`if a < 0 then -a else a`, so in particular `Int64.minValue` will be mapped to `Int64.minValue`. -/
@[extern "lean_int64_abs"]
def Int64.abs (a : Int64) : Int64 := ⟨⟨a.toBitVec.abs⟩⟩

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

@[extern "lean_bool_to_int64"]
def Bool.toInt64 (b : Bool) : Int64 := if b then 1 else 0

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

theorem ISize.toBitVec.inj : {x y : ISize} → x.toBitVec = y.toBitVec → x = y
  | ⟨⟨_⟩⟩, ⟨⟨_⟩⟩, rfl => rfl

/-- Obtains the `ISize` that is 2's complement equivalent to the `USize`. -/
@[inline] def USize.toISize (i : USize) : ISize := ISize.ofUSize i
@[inline, deprecated USize.toISize (since := "2025-02-13"), inherit_doc USize.toISize]
def ISize.mk (i : USize) : ISize := USize.toISize i
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
@[inline] def ISize.toNatClampNeg (i : ISize) : Nat := i.toInt.toNat
@[inline, deprecated ISize.toNatClampNeg (since := "2025-02-13"), inherit_doc ISize.toNatClampNeg]
def ISize.toNat (i : ISize) : Nat := i.toInt.toNat
/-- Obtains the `ISize` whose 2's complement representation is the given `BitVec`. -/
@[inline] def ISize.ofBitVec (b : BitVec System.Platform.numBits) : ISize := ⟨⟨b⟩⟩
@[extern "lean_isize_to_int8"]
def ISize.toInt8 (a : ISize) : Int8 := ⟨⟨a.toBitVec.signExtend 8⟩⟩
@[extern "lean_isize_to_int16"]
def ISize.toInt16 (a : ISize) : Int16 := ⟨⟨a.toBitVec.signExtend 16⟩⟩
@[extern "lean_isize_to_int32"]
def ISize.toInt32 (a : ISize) : Int32 := ⟨⟨a.toBitVec.signExtend 32⟩⟩
/--
Upcasts `ISize` to `Int64`. This function is lossless as `ISize` is either `Int32` or `Int64`.
-/
@[extern "lean_isize_to_int64"]
def ISize.toInt64 (a : ISize) : Int64 := ⟨⟨a.toBitVec.signExtend 64⟩⟩
@[extern "lean_int8_to_isize"]
def Int8.toISize (a : Int8) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
@[extern "lean_int16_to_isize"]
def Int16.toISize (a : Int16) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
/--
Upcasts `Int32` to `ISize`. This function is lossless as `ISize` is either `Int32` or `Int64`.
-/
@[extern "lean_int32_to_isize"]
def Int32.toISize (a : Int32) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
@[extern "lean_int64_to_isize"]
def Int64.toISize (a : Int64) : ISize := ⟨⟨a.toBitVec.signExtend System.Platform.numBits⟩⟩
@[extern "lean_isize_neg"]
def ISize.neg (i : ISize) : ISize := ⟨⟨-i.toBitVec⟩⟩

instance : ToString ISize where
  toString i := toString i.toInt
instance : Repr ISize where
  reprPrec i prec := reprPrec i.toInt prec
instance : ReprAtom ISize := ⟨⟩

instance : Hashable ISize where
  hash i := i.toUSize.toUInt64

instance ISize.instOfNat : OfNat ISize n := ⟨ISize.ofNat n⟩
instance ISize.instNeg : Neg ISize where
  neg := ISize.neg

/-- The maximum value an `ISize` may attain, that is, `2^(System.Platform.numBits - 1) - 1`. -/
abbrev ISize.maxValue : ISize := .ofInt (2 ^ (System.Platform.numBits - 1) - 1)
/-- The minimum value an `ISize` may attain, that is, `-2^(System.Platform.numBits - 1)`. -/
abbrev ISize.minValue : ISize := .ofInt (-2 ^ (System.Platform.numBits - 1))

/-- Constructs an `ISize` from an `Int` which is known to be in bounds. -/
@[inline]
def ISize.ofIntLE (i : Int) (_hl : ISize.minValue.toInt ≤ i) (_hr : i ≤ ISize.maxValue.toInt) : ISize :=
  ISize.ofInt i
/-- Constructs an `ISize` from an `Int`, clamping if the value is too small or too large. -/
def ISize.ofIntTruncate (i : Int) : ISize :=
  if hl : ISize.minValue.toInt ≤ i then
    if hr : i ≤ ISize.maxValue.toInt then
      ISize.ofIntLE i hl hr
    else
      ISize.minValue
  else
    ISize.minValue

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
/-- Computes the absolute value of the signed integer. This function is equivalent to
`if a < 0 then -a else a`, so in particular `ISize.minValue` will be mapped to `ISize.minValue`. -/
@[extern "lean_isize_abs"]
def ISize.abs (a : ISize) : ISize := ⟨⟨a.toBitVec.abs⟩⟩

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

@[extern "lean_bool_to_isize"]
def Bool.toISize (b : Bool) : ISize := if b then 1 else 0

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
