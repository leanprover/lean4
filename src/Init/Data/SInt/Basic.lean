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

/-- The size of type `Int8`, that is, `2^8 = 256`. -/
abbrev Int8.size : Nat := 256

/--
Obtain the `BitVec` that contains the 2's complement representation of the `Int8`.
-/
@[inline] def Int8.toBitVec (x : Int8) : BitVec 8 := x.toUInt8.toBitVec

@[extern "lean_int8_of_int"]
def Int8.ofInt (i : @& Int) : Int8 := ⟨⟨BitVec.ofInt 8 i⟩⟩
@[extern "lean_int8_of_int"]
def Int8.ofNat (n : @& Nat) : Int8 := ⟨⟨BitVec.ofNat 8 n⟩⟩
abbrev Int.toInt8 := Int8.ofInt
abbrev Nat.toInt8 := Int8.ofNat
@[extern "lean_int8_to_int"]
def Int8.toInt (i : Int8) : Int := i.toBitVec.toInt
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
def Int8.mod (a b : Int8) : Int8 := ⟨⟨BitVec.smod a.toBitVec b.toBitVec⟩⟩
@[extern "lean_int8_land"]
def Int8.land (a b : Int8) : Int8 := ⟨⟨a.toBitVec &&& b.toBitVec⟩⟩
@[extern "lean_int8_lor"]
def Int8.lor (a b : Int8) : Int8 := ⟨⟨a.toBitVec ||| b.toBitVec⟩⟩
@[extern "lean_int8_xor"]
def Int8.xor (a b : Int8) : Int8 := ⟨⟨a.toBitVec ^^^ b.toBitVec⟩⟩
@[extern "lean_int8_shift_left"]
def Int8.shiftLeft (a b : Int8) : Int8 := ⟨⟨a.toBitVec <<< (mod b 8).toBitVec⟩⟩
@[extern "lean_int8_shift_right"]
def Int8.shiftRight (a b : Int8) : Int8 := ⟨⟨BitVec.sshiftRight' a.toBitVec (mod b 8).toBitVec⟩⟩
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
