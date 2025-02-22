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

/-- Converts a `UInt8` into the corresponding `Fin UInt8.size`. -/
def UInt8.toFin (x : UInt8) : Fin UInt8.size := x.toBitVec.toFin
@[deprecated UInt8.toFin (since := "2025-02-12"), inherit_doc UInt8.toFin]
def UInt8.val (x : UInt8) : Fin UInt8.size := x.toFin
@[extern "lean_uint8_of_nat"]
def UInt8.ofNat (n : @& Nat) : UInt8 := ⟨BitVec.ofNat 8 n⟩
/--
Converts the given natural number to `UInt8`, but returns `2^8 - 1` for natural numbers `>= 2^8`.
-/
def UInt8.ofNatTruncate (n : Nat) : UInt8 :=
  if h : n < UInt8.size then
    UInt8.ofNatLT n h
  else
    UInt8.ofNatLT (UInt8.size - 1) (by decide)
abbrev Nat.toUInt8 := UInt8.ofNat
@[extern "lean_uint8_to_nat"]
def UInt8.toNat (n : UInt8) : Nat := n.toBitVec.toNat

instance UInt8.instOfNat : OfNat UInt8 n := ⟨UInt8.ofNat n⟩

/-- Converts a `UInt16` into the corresponding `Fin UInt16.size`. -/
def UInt16.toFin (x : UInt16) : Fin UInt16.size := x.toBitVec.toFin
@[deprecated UInt16.toFin (since := "2025-02-12"), inherit_doc UInt16.toFin]
def UInt16.val (x : UInt16) : Fin UInt16.size := x.toFin
@[extern "lean_uint16_of_nat"]
def UInt16.ofNat (n : @& Nat) : UInt16 := ⟨BitVec.ofNat 16 n⟩
/--
Converts the given natural number to `UInt16`, but returns `2^16 - 1` for natural numbers `>= 2^16`.
-/
def UInt16.ofNatTruncate (n : Nat) : UInt16 :=
  if h : n < UInt16.size then
    UInt16.ofNatLT n h
  else
    UInt16.ofNatLT (UInt16.size - 1) (by decide)
abbrev Nat.toUInt16 := UInt16.ofNat
@[extern "lean_uint16_to_nat"]
def UInt16.toNat (n : UInt16) : Nat := n.toBitVec.toNat
@[extern "lean_uint16_to_uint8"]
def UInt16.toUInt8 (a : UInt16) : UInt8 := a.toNat.toUInt8
@[extern "lean_uint8_to_uint16"]
def UInt8.toUInt16 (a : UInt8) : UInt16 := ⟨⟨a.toNat, Nat.lt_trans a.toBitVec.isLt (by decide)⟩⟩

instance UInt16.instOfNat : OfNat UInt16 n := ⟨UInt16.ofNat n⟩

/-- Converts a `UInt32` into the corresponding `Fin UInt32.size`. -/
def UInt32.toFin (x : UInt32) : Fin UInt32.size := x.toBitVec.toFin
@[deprecated UInt32.toFin (since := "2025-02-12"), inherit_doc UInt32.toFin]
def UInt32.val (x : UInt32) : Fin UInt32.size := x.toFin
@[extern "lean_uint32_of_nat"]
def UInt32.ofNat (n : @& Nat) : UInt32 := ⟨BitVec.ofNat 32 n⟩
@[inline, deprecated UInt32.ofNatLT (since := "2025-02-13"), inherit_doc UInt32.ofNatLT]
def UInt32.ofNat' (n : Nat) (h : n < UInt32.size) : UInt32 := UInt32.ofNatLT n h
/--
Converts the given natural number to `UInt32`, but returns `2^32 - 1` for natural numbers `>= 2^32`.
-/
def UInt32.ofNatTruncate (n : Nat) : UInt32 :=
  if h : n < UInt32.size then
    UInt32.ofNatLT n h
  else
    UInt32.ofNatLT (UInt32.size - 1) (by decide)
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

theorem UInt32.ofNatLT_lt_of_lt {n m : Nat} (h1 : n < UInt32.size) (h2 : m < UInt32.size) :
     n < m → UInt32.ofNatLT n h1 < UInt32.ofNat m := by
  simp only [(· < ·), BitVec.toNat, ofNatLT, BitVec.ofNatLT, ofNat, BitVec.ofNat, Fin.ofNat',
    Nat.mod_eq_of_lt h2, imp_self]

@[deprecated UInt32.ofNatLT_lt_of_lt (since := "2025-02-13")]
theorem UInt32.ofNat'_lt_of_lt {n m : Nat} (h1 : n < UInt32.size) (h2 : m < UInt32.size) :
     n < m → UInt32.ofNatLT n h1 < UInt32.ofNat m := UInt32.ofNatLT_lt_of_lt h1 h2

theorem UInt32.lt_ofNatLT_of_lt {n m : Nat} (h1 : n < UInt32.size) (h2 : m < UInt32.size) :
     m < n → UInt32.ofNat m < UInt32.ofNatLT n h1 := by
  simp only [(· < ·), BitVec.toNat, ofNatLT, BitVec.ofNatLT, ofNat, BitVec.ofNat, Fin.ofNat',
    Nat.mod_eq_of_lt h2, imp_self]

@[deprecated UInt32.lt_ofNatLT_of_lt (since := "2025-02-13")]
theorem UInt32.lt_ofNat'_of_lt {n m : Nat} (h1 : n < UInt32.size) (h2 : m < UInt32.size) :
     m < n → UInt32.ofNat m < UInt32.ofNatLT n h1 := UInt32.lt_ofNatLT_of_lt h1 h2

/-- Converts a `UInt64` into the corresponding `Fin UInt64.size`. -/
def UInt64.toFin (x : UInt64) : Fin UInt64.size := x.toBitVec.toFin
@[deprecated UInt64.toFin (since := "2025-02-12"), inherit_doc UInt64.toFin]
def UInt64.val (x : UInt64) : Fin UInt64.size := x.toFin
@[extern "lean_uint64_of_nat"]
def UInt64.ofNat (n : @& Nat) : UInt64 := ⟨BitVec.ofNat 64 n⟩
/--
Converts the given natural number to `UInt64`, but returns `2^64 - 1` for natural numbers `>= 2^64`.
-/
def UInt64.ofNatTruncate (n : Nat) : UInt64 :=
  if h : n < UInt64.size then
    UInt64.ofNatLT n h
  else
    UInt64.ofNatLT (UInt64.size - 1) (by decide)
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

@[deprecated usize_size_pos (since := "2024-11-24")] theorem usize_size_gt_zero : USize.size > 0 :=
  usize_size_pos

/-- Converts a `USize` into the corresponding `Fin USize.size`. -/
def USize.toFin (x : USize) : Fin USize.size := x.toBitVec.toFin
@[deprecated USize.toFin (since := "2025-02-12"), inherit_doc USize.toFin]
def USize.val (x : USize) : Fin USize.size := x.toFin
@[extern "lean_usize_of_nat"]
def USize.ofNat (n : @& Nat) : USize := ⟨BitVec.ofNat _ n⟩
/--
Converts the given natural number to `USize`, but returns `USize.size - 1` (i.e., `2^64 - 1` or
`2^32 - 1` depending on the platform) for natural numbers `>= USize.size`.
-/
def USize.ofNatTruncate (n : Nat) : USize :=
  if h : n < USize.size then
    USize.ofNatLT n h
  else
    USize.ofNatLT (USize.size - 1) (Nat.pred_lt (Nat.ne_zero_of_lt usize_size_pos))
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
