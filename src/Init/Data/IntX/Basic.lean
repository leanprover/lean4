/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.UInt.Basic

structure Int8 where
  toUInt8 : UInt8

abbrev Int8.size : Nat := UInt8.size

-- two's complement interpretation of the Int8
@[inline] def Int8.toBitVec (x : Int8) : BitVec 8 := x.toUInt8.toBitVec

@[extern "lean_int8_of_int"]
def Int8.ofInt (i : @& Int) : Int8 := ⟨⟨BitVec.ofInt 8 i⟩⟩
@[extern "lean_int8_of_int"]
def Int8.ofNat (n : @& Nat) : Int8 := ⟨⟨BitVec.ofNat 8 n⟩⟩
abbrev Int.toInt8 := Int8.ofInt
abbrev Nat.toInt8 := Int8.ofNat
@[extern "lean_int8_to_int"]
def Int8.toInt (i : Int8) : Int := i.toBitVec.toInt
-- TODO: should this be tagged with extern?
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

