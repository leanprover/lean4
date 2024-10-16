/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.UInt.Basic

structure Int8 where
  toUInt8 : UInt8

structure Int16 where
  toUInt16 : UInt16

structure Int32 where
  toUInt32 : UInt32

structure Int64 where
  toUInt64 : UInt64

structure ISize where
  toUSize : USize

abbrev Int8.size : Nat := UInt8.size
abbrev Int16.size : Nat := UInt16.size
abbrev Int32.size : Nat := UInt32.size
abbrev Int64.size : Nat := UInt64.size
abbrev ISize.size : Nat := USize.size

def Int8.toBitVec (x : Int8) : BitVec 8 := x.toUInt8.toBitVec
def Int16.toBitVec (x : Int16) : BitVec 16 := x.toUInt16.toBitVec
def Int32.toBitVec (x : Int32) : BitVec 32 := x.toUInt32.toBitVec
def Int64.toBitVec (x : Int64) : BitVec 64 := x.toUInt64.toBitVec
def ISize.toBitVec (x : ISize) : BitVec System.Platform.numBits := x.toUSize.toBitVec

/-
TODO: define BasicAux functions:
  - val
  - ofNat
  - toNat
TODO: define first Basic functions:
  - arithmetic only for now
-/

/-
def Int8.val (x : Int8) : Fin Int8.size := x.toBitVec.toFin
def Int8.ofNat (n : @& Nat) : Int8 := ⟨BitVec.ofNat 8 n⟩
abbrev Nat.toInt8 := Int8.ofNat
def Int8.toNat (n : Int8) : Nat := n.toBitVec.toNat

instance Int8.instOfNat : OfNat Int8 n := ⟨Int8.ofNat n⟩

def Int16.val (x : Int16) : Fin Int16.size := x.toBitVec.toFin
def Int16.ofNat (n : @& Nat) : Int16 := ⟨BitVec.ofNat 16 n⟩
abbrev Nat.toInt16 := Int16.ofNat
def Int16.toNat (n : Int16) : Nat := n.toBitVec.toNat
def Int16.toInt8 (a : Int16) : Int8 := a.toNat.toInt8
def Int8.toInt16 (a : Int8) : Int16 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

instance Int16.instOfNat : OfNat Int16 n := ⟨Int16.ofNat n⟩

def Int32.val (x : Int32) : Fin Int32.size := x.toBitVec.toFin
def Int32.ofNat (n : @& Nat) : Int32 := ⟨BitVec.ofNat 32 n⟩
def Int32.ofNat' (n : Nat) (h : n < Int32.size) : Int32 := ⟨BitVec.ofNatLt n h⟩
abbrev Nat.toInt32 := Int32.ofNat
def Int32.toInt8 (a : Int32) : Int8 := a.toNat.toInt8
def Int32.toInt16 (a : Int32) : Int16 := a.toNat.toInt16
def Int8.toInt32 (a : Int8) : Int32 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
def Int16.toInt32 (a : Int16) : Int32 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

instance Int32.instOfNat : OfNat Int32 n := ⟨Int32.ofNat n⟩

def Int64.val (x : Int64) : Fin Int64.size := x.toBitVec.toFin
def Int64.ofNat (n : @& Nat) : Int64 := ⟨BitVec.ofNat 64 n⟩
abbrev Nat.toInt64 := Int64.ofNat
def Int64.toNat (n : Int64) : Nat := n.toBitVec.toNat
def Int64.toInt8 (a : Int64) : Int8 := a.toNat.toInt8
def Int64.toInt16 (a : Int64) : Int16 := a.toNat.toInt16
def Int64.toInt32 (a : Int64) : Int32 := a.toNat.toInt32
def Int8.toInt64 (a : Int8) : Int64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
def Int16.toInt64 (a : Int16) : Int64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
def Int32.toInt64 (a : Int32) : Int64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

instance Int64.instOfNat : OfNat Int64 n := ⟨Int64.ofNat n⟩
-/
