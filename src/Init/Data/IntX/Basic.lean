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
def Int8.toInt (n : Int8) : Int := n.toBitVec.toInt
-- TODO: should this be tagged with extern?
def Int8.toNat (n : Int8) : Nat := n.toInt.toNat

instance : OfNat Int8 n := ⟨Int8.ofNat n⟩
