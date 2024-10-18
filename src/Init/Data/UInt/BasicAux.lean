/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Fin.Basic
import Init.Data.BitVec.BasicAux

/-!
This module exists to provide the very basic `UInt8` etc. definitions required for
`Init.Data.Char.Basic` and `Init.Data.Array.Basic`. These are very important as they are used in
meta code that is then (transitively) used in `Init.Data.UInt.Basic` and `Init.Data.BitVec.Basic`.
This file thus breaks the import cycle that would be created by this dependency.
-/

open Nat

def UInt8.val (x : UInt8) : Fin UInt8.size := x.toBitVec.toFin
@[extern "lean_uint8_of_nat"]
def UInt8.ofNat (n : @& Nat) : UInt8 := ⟨BitVec.ofNat 8 n⟩
abbrev Nat.toUInt8 := UInt8.ofNat
@[extern "lean_uint8_to_nat"]
def UInt8.toNat (n : UInt8) : Nat := n.toBitVec.toNat

instance UInt8.instOfNat : OfNat UInt8 n := ⟨UInt8.ofNat n⟩

def UInt16.val (x : UInt16) : Fin UInt16.size := x.toBitVec.toFin
@[extern "lean_uint16_of_nat"]
def UInt16.ofNat (n : @& Nat) : UInt16 := ⟨BitVec.ofNat 16 n⟩
abbrev Nat.toUInt16 := UInt16.ofNat
@[extern "lean_uint16_to_nat"]
def UInt16.toNat (n : UInt16) : Nat := n.toBitVec.toNat
@[extern "lean_uint16_to_uint8"]
def UInt16.toUInt8 (a : UInt16) : UInt8 := a.toNat.toUInt8
@[extern "lean_uint8_to_uint16"]
def UInt8.toUInt16 (a : UInt8) : UInt16 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

instance UInt16.instOfNat : OfNat UInt16 n := ⟨UInt16.ofNat n⟩

def UInt32.val (x : UInt32) : Fin UInt32.size := x.toBitVec.toFin
@[extern "lean_uint32_of_nat"]
def UInt32.ofNat (n : @& Nat) : UInt32 := ⟨BitVec.ofNat 32 n⟩
@[extern "lean_uint32_of_nat"]
def UInt32.ofNat' (n : Nat) (h : n < UInt32.size) : UInt32 := ⟨BitVec.ofNatLt n h⟩
/--
Converts the given natural number to `UInt32`, but returns `2^32 - 1` for natural numbers `>= 2^32`.
-/
def UInt32.ofNatTruncate (n : Nat) : UInt32 :=
  if h : n < UInt32.size then
    UInt32.ofNat' n h
  else
    UInt32.ofNat' (UInt32.size - 1) (by decide)
abbrev Nat.toUInt32 := UInt32.ofNat
@[extern "lean_uint32_to_uint8"]
def UInt32.toUInt8 (a : UInt32) : UInt8 := a.toNat.toUInt8
@[extern "lean_uint32_to_uint16"]
def UInt32.toUInt16 (a : UInt32) : UInt16 := a.toNat.toUInt16
@[extern "lean_uint8_to_uint32"]
def UInt8.toUInt32 (a : UInt8) : UInt32 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
@[extern "lean_uint16_to_uint32"]
def UInt16.toUInt32 (a : UInt16) : UInt32 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

instance UInt32.instOfNat : OfNat UInt32 n := ⟨UInt32.ofNat n⟩

theorem UInt32.ofNat'_lt_of_lt {n m : Nat} (h1 : n < UInt32.size) (h2 : m < UInt32.size) :
     n < m → UInt32.ofNat' n h1 < UInt32.ofNat m := by
  simp only [(· < ·), BitVec.toNat, ofNat', BitVec.ofNatLt, ofNat, BitVec.ofNat, Fin.ofNat',
    Nat.mod_eq_of_lt h2, imp_self]

theorem UInt32.lt_ofNat'_of_lt {n m : Nat} (h1 : n < UInt32.size) (h2 : m < UInt32.size) :
     m < n → UInt32.ofNat m < UInt32.ofNat' n h1  := by
  simp only [(· < ·), BitVec.toNat, ofNat', BitVec.ofNatLt, ofNat, BitVec.ofNat, Fin.ofNat',
    Nat.mod_eq_of_lt h2, imp_self]

def UInt64.val (x : UInt64) : Fin UInt64.size := x.toBitVec.toFin
@[extern "lean_uint64_of_nat"]
def UInt64.ofNat (n : @& Nat) : UInt64 := ⟨BitVec.ofNat 64 n⟩
abbrev Nat.toUInt64 := UInt64.ofNat
@[extern "lean_uint64_to_nat"]
def UInt64.toNat (n : UInt64) : Nat := n.toBitVec.toNat
@[extern "lean_uint64_to_uint8"]
def UInt64.toUInt8 (a : UInt64) : UInt8 := a.toNat.toUInt8
@[extern "lean_uint64_to_uint16"]
def UInt64.toUInt16 (a : UInt64) : UInt16 := a.toNat.toUInt16
@[extern "lean_uint64_to_uint32"]
def UInt64.toUInt32 (a : UInt64) : UInt32 := a.toNat.toUInt32
@[extern "lean_uint8_to_uint64"]
def UInt8.toUInt64 (a : UInt8) : UInt64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
@[extern "lean_uint16_to_uint64"]
def UInt16.toUInt64 (a : UInt16) : UInt64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩
@[extern "lean_uint32_to_uint64"]
def UInt32.toUInt64 (a : UInt32) : UInt64 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

instance UInt64.instOfNat : OfNat UInt64 n := ⟨UInt64.ofNat n⟩

theorem usize_size_gt_zero : USize.size > 0 := by
  cases usize_size_eq with
  | inl h => rw [h]; decide
  | inr h => rw [h]; decide

def USize.val (x : USize) : Fin USize.size := x.toBitVec.toFin
@[extern "lean_usize_of_nat"]
def USize.ofNat (n : @& Nat) : USize := ⟨BitVec.ofNat _ n⟩
abbrev Nat.toUSize := USize.ofNat
@[extern "lean_usize_to_nat"]
def USize.toNat (n : USize) : Nat := n.toBitVec.toNat
@[extern "lean_usize_add"]
def USize.add (a b : USize) : USize := ⟨a.toBitVec + b.toBitVec⟩
@[extern "lean_usize_sub"]
def USize.sub (a b : USize) : USize := ⟨a.toBitVec - b.toBitVec⟩

def USize.lt (a b : USize) : Prop := a.toBitVec < b.toBitVec
def USize.le (a b : USize) : Prop := a.toBitVec ≤ b.toBitVec

instance USize.instOfNat : OfNat USize n := ⟨USize.ofNat n⟩

instance : Add USize       := ⟨USize.add⟩
instance : Sub USize       := ⟨USize.sub⟩
instance : LT USize        := ⟨USize.lt⟩
instance : LE USize        := ⟨USize.le⟩

@[extern "lean_usize_dec_lt"]
def USize.decLt (a b : USize) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toBitVec < b.toBitVec))

@[extern "lean_usize_dec_le"]
def USize.decLe (a b : USize) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toBitVec ≤ b.toBitVec))

instance (a b : USize) : Decidable (a < b) := USize.decLt a b
instance (a b : USize) : Decidable (a ≤ b) := USize.decLe a b
