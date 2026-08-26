/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kim Morrison
-/
module

prelude
public import Init.Data.ByteArray.Pack
import Init.Data.ByteArray.Lemmas
import Init.Data.UInt
import Init.Data.BitVec
import Init.Omega

public section

namespace ByteArray

/-! ### `size` is preserved by writes -/

@[simp] theorem size_setUInt16LE! (a : ByteArray) (off : Nat) (v : UInt16) :
    (a.setUInt16LE! off v).size = a.size := by unfold setUInt16LE!; split <;> simp
@[simp] theorem size_setUInt16BE! (a : ByteArray) (off : Nat) (v : UInt16) :
    (a.setUInt16BE! off v).size = a.size := by unfold setUInt16BE!; split <;> simp
@[simp] theorem size_setUInt32LE! (a : ByteArray) (off : Nat) (v : UInt32) :
    (a.setUInt32LE! off v).size = a.size := by unfold setUInt32LE!; split <;> simp
@[simp] theorem size_setUInt32BE! (a : ByteArray) (off : Nat) (v : UInt32) :
    (a.setUInt32BE! off v).size = a.size := by unfold setUInt32BE!; split <;> simp
@[simp] theorem size_setUInt64LE! (a : ByteArray) (off : Nat) (v : UInt64) :
    (a.setUInt64LE! off v).size = a.size := by unfold setUInt64LE!; split <;> simp
@[simp] theorem size_setUInt64BE! (a : ByteArray) (off : Nat) (v : UInt64) :
    (a.setUInt64BE! off v).size = a.size := by unfold setUInt64BE!; split <;> simp

/-! ### Round-trip: reading back a written value

These reduce the read of the freshly-written bytes to a fixed-width
bit-recombination identity, discharged by `getLsbD` extensionality. -/

theorem getUInt16LE!_setUInt16LE!_self (a : ByteArray) (off : Nat) (v : UInt16)
    (h : off + 2 ≤ a.size) : (a.setUInt16LE! off v).getUInt16LE! off = v := by
  unfold getUInt16LE! setUInt16LE!
  rw [if_pos h]
  simp only [size_set!, get!_eq_getElem!]
  rw [if_pos h]
  simp (disch := (first | omega | (simp only [size_set!]; omega))) only
    [getElem!_set!_self, getElem!_set!_ne]
  apply UInt16.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt16.toBitVec_or, UInt16.toBitVec_shiftLeft, UInt16.toBitVec_shiftRight,
    UInt16.toBitVec_toUInt8, UInt8.toBitVec_toUInt16, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.toNat_umod]
  by_cases h0 : i < 8 <;>
    first | omega | (cases hb : v.toBitVec[i] <;> simp_all <;> omega)

theorem getUInt16BE!_setUInt16BE!_self (a : ByteArray) (off : Nat) (v : UInt16)
    (h : off + 2 ≤ a.size) : (a.setUInt16BE! off v).getUInt16BE! off = v := by
  unfold getUInt16BE! setUInt16BE!
  rw [if_pos h]
  simp only [size_set!, get!_eq_getElem!]
  rw [if_pos h]
  simp (disch := (first | omega | (simp only [size_set!]; omega))) only
    [getElem!_set!_self, getElem!_set!_ne]
  apply UInt16.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt16.toBitVec_or, UInt16.toBitVec_shiftLeft, UInt16.toBitVec_shiftRight,
    UInt16.toBitVec_toUInt8, UInt8.toBitVec_toUInt16, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.toNat_umod]
  by_cases h0 : i < 8 <;>
    first | omega | (cases hb : v.toBitVec[i] <;> simp_all <;> omega)

theorem getUInt32LE!_setUInt32LE!_self (a : ByteArray) (off : Nat) (v : UInt32)
    (h : off + 4 ≤ a.size) : (a.setUInt32LE! off v).getUInt32LE! off = v := by
  unfold getUInt32LE! setUInt32LE!
  rw [if_pos h]
  simp only [size_set!, get!_eq_getElem!]
  rw [if_pos h]
  simp (disch := (first | omega | (simp only [size_set!]; omega))) only
    [getElem!_set!_self, getElem!_set!_ne]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.toNat_umod]
  by_cases h0 : i < 8 <;> by_cases h1 : i < 16 <;> by_cases h2 : i < 24 <;>
    first | omega | (cases hb : v.toBitVec[i] <;> simp_all <;> omega)

theorem getUInt32BE!_setUInt32BE!_self (a : ByteArray) (off : Nat) (v : UInt32)
    (h : off + 4 ≤ a.size) : (a.setUInt32BE! off v).getUInt32BE! off = v := by
  unfold getUInt32BE! setUInt32BE!
  rw [if_pos h]
  simp only [size_set!, get!_eq_getElem!]
  rw [if_pos h]
  simp (disch := (first | omega | (simp only [size_set!]; omega))) only
    [getElem!_set!_self, getElem!_set!_ne]
  apply UInt32.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight,
    UInt32.toBitVec_toUInt8, UInt8.toBitVec_toUInt32, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.toNat_umod]
  by_cases h0 : i < 8 <;> by_cases h1 : i < 16 <;> by_cases h2 : i < 24 <;>
    first | omega | (cases hb : v.toBitVec[i] <;> simp_all <;> omega)

theorem getUInt64LE!_setUInt64LE!_self (a : ByteArray) (off : Nat) (v : UInt64)
    (h : off + 8 ≤ a.size) : (a.setUInt64LE! off v).getUInt64LE! off = v := by
  unfold getUInt64LE! setUInt64LE!
  rw [if_pos h]
  simp only [size_set!, get!_eq_getElem!]
  rw [if_pos h]
  simp (disch := (first | omega | (simp only [size_set!]; omega))) only
    [getElem!_set!_self, getElem!_set!_ne]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_toUInt8, UInt8.toBitVec_toUInt64, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.toNat_umod]
  by_cases h0 : i < 8 <;> by_cases h1 : i < 16 <;> by_cases h2 : i < 24 <;> by_cases h3 : i < 32 <;>
   by_cases h4 : i < 40 <;> by_cases h5 : i < 48 <;> by_cases h6 : i < 56 <;>
    first | omega | (cases hb : v.toBitVec[i] <;> simp_all <;> omega)

theorem getUInt64BE!_setUInt64BE!_self (a : ByteArray) (off : Nat) (v : UInt64)
    (h : off + 8 ≤ a.size) : (a.setUInt64BE! off v).getUInt64BE! off = v := by
  unfold getUInt64BE! setUInt64BE!
  rw [if_pos h]
  simp only [size_set!, get!_eq_getElem!]
  rw [if_pos h]
  simp (disch := (first | omega | (simp only [size_set!]; omega))) only
    [getElem!_set!_self, getElem!_set!_ne]
  apply UInt64.toBitVec_inj.mp
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_toUInt8, UInt8.toBitVec_toUInt64, BitVec.shiftLeft_eq', BitVec.ushiftRight_eq',
    BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_setWidth, BitVec.toNat_umod]
  by_cases h0 : i < 8 <;> by_cases h1 : i < 16 <;> by_cases h2 : i < 24 <;> by_cases h3 : i < 32 <;>
   by_cases h4 : i < 40 <;> by_cases h5 : i < 48 <;> by_cases h6 : i < 56 <;>
    first | omega | (cases hb : v.toBitVec[i] <;> simp_all <;> omega)

/-! ### Disjoint-window invariance

`getElem!_setUIntWE!_of_outside` is the general fact: a wide write changes only
the bytes in its own `[o, o + W/8)` window, so a read of any byte — and hence a
read of any width or endianness — that lies entirely outside that window is
unaffected. The `_of_disjoint` lemmas below specialize this to a read of the
same width and endianness. -/

theorem getElem!_setUInt16LE!_of_outside (a : ByteArray) (o j : Nat) (v : UInt16)
    (h : j < o ∨ o + 2 ≤ j) : (a.setUInt16LE! o v)[j]! = a[j]! := by
  unfold setUInt16LE!
  split
  · simp (disch := (first | omega | (simp only [size_set!]; omega))) only [getElem!_set!_ne]
  · rfl

theorem getElem!_setUInt16BE!_of_outside (a : ByteArray) (o j : Nat) (v : UInt16)
    (h : j < o ∨ o + 2 ≤ j) : (a.setUInt16BE! o v)[j]! = a[j]! := by
  unfold setUInt16BE!
  split
  · simp (disch := (first | omega | (simp only [size_set!]; omega))) only [getElem!_set!_ne]
  · rfl

theorem getElem!_setUInt32LE!_of_outside (a : ByteArray) (o j : Nat) (v : UInt32)
    (h : j < o ∨ o + 4 ≤ j) : (a.setUInt32LE! o v)[j]! = a[j]! := by
  unfold setUInt32LE!
  split
  · simp (disch := (first | omega | (simp only [size_set!]; omega))) only [getElem!_set!_ne]
  · rfl

theorem getElem!_setUInt32BE!_of_outside (a : ByteArray) (o j : Nat) (v : UInt32)
    (h : j < o ∨ o + 4 ≤ j) : (a.setUInt32BE! o v)[j]! = a[j]! := by
  unfold setUInt32BE!
  split
  · simp (disch := (first | omega | (simp only [size_set!]; omega))) only [getElem!_set!_ne]
  · rfl

theorem getElem!_setUInt64LE!_of_outside (a : ByteArray) (o j : Nat) (v : UInt64)
    (h : j < o ∨ o + 8 ≤ j) : (a.setUInt64LE! o v)[j]! = a[j]! := by
  unfold setUInt64LE!
  split
  · simp (disch := (first | omega | (simp only [size_set!]; omega))) only [getElem!_set!_ne]
  · rfl

theorem getElem!_setUInt64BE!_of_outside (a : ByteArray) (o j : Nat) (v : UInt64)
    (h : j < o ∨ o + 8 ≤ j) : (a.setUInt64BE! o v)[j]! = a[j]! := by
  unfold setUInt64BE!
  split
  · simp (disch := (first | omega | (simp only [size_set!]; omega))) only [getElem!_set!_ne]
  · rfl

theorem getUInt16LE!_setUInt16LE!_of_disjoint (a : ByteArray) (o₁ o₂ : Nat) (v : UInt16)
    (h₂ : o₂ + 2 ≤ a.size) (hd : o₂ + 2 ≤ o₁ ∨ o₁ + 2 ≤ o₂) :
    (a.setUInt16LE! o₁ v).getUInt16LE! o₂ = a.getUInt16LE! o₂ := by
  unfold getUInt16LE!
  simp only [size_setUInt16LE!, get!_eq_getElem!]
  rw [if_pos h₂, if_pos h₂,
      getElem!_setUInt16LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt16LE!_of_outside _ _ _ _ (by omega)]

theorem getUInt16BE!_setUInt16BE!_of_disjoint (a : ByteArray) (o₁ o₂ : Nat) (v : UInt16)
    (h₂ : o₂ + 2 ≤ a.size) (hd : o₂ + 2 ≤ o₁ ∨ o₁ + 2 ≤ o₂) :
    (a.setUInt16BE! o₁ v).getUInt16BE! o₂ = a.getUInt16BE! o₂ := by
  unfold getUInt16BE!
  simp only [size_setUInt16BE!, get!_eq_getElem!]
  rw [if_pos h₂, if_pos h₂,
      getElem!_setUInt16BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt16BE!_of_outside _ _ _ _ (by omega)]

theorem getUInt32LE!_setUInt32LE!_of_disjoint (a : ByteArray) (o₁ o₂ : Nat) (v : UInt32)
    (h₂ : o₂ + 4 ≤ a.size) (hd : o₂ + 4 ≤ o₁ ∨ o₁ + 4 ≤ o₂) :
    (a.setUInt32LE! o₁ v).getUInt32LE! o₂ = a.getUInt32LE! o₂ := by
  unfold getUInt32LE!
  simp only [size_setUInt32LE!, get!_eq_getElem!]
  rw [if_pos h₂, if_pos h₂,
      getElem!_setUInt32LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt32LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt32LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt32LE!_of_outside _ _ _ _ (by omega)]

theorem getUInt32BE!_setUInt32BE!_of_disjoint (a : ByteArray) (o₁ o₂ : Nat) (v : UInt32)
    (h₂ : o₂ + 4 ≤ a.size) (hd : o₂ + 4 ≤ o₁ ∨ o₁ + 4 ≤ o₂) :
    (a.setUInt32BE! o₁ v).getUInt32BE! o₂ = a.getUInt32BE! o₂ := by
  unfold getUInt32BE!
  simp only [size_setUInt32BE!, get!_eq_getElem!]
  rw [if_pos h₂, if_pos h₂,
      getElem!_setUInt32BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt32BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt32BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt32BE!_of_outside _ _ _ _ (by omega)]

theorem getUInt64LE!_setUInt64LE!_of_disjoint (a : ByteArray) (o₁ o₂ : Nat) (v : UInt64)
    (h₂ : o₂ + 8 ≤ a.size) (hd : o₂ + 8 ≤ o₁ ∨ o₁ + 8 ≤ o₂) :
    (a.setUInt64LE! o₁ v).getUInt64LE! o₂ = a.getUInt64LE! o₂ := by
  unfold getUInt64LE!
  simp only [size_setUInt64LE!, get!_eq_getElem!]
  rw [if_pos h₂, if_pos h₂,
      getElem!_setUInt64LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64LE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64LE!_of_outside _ _ _ _ (by omega)]

theorem getUInt64BE!_setUInt64BE!_of_disjoint (a : ByteArray) (o₁ o₂ : Nat) (v : UInt64)
    (h₂ : o₂ + 8 ≤ a.size) (hd : o₂ + 8 ≤ o₁ ∨ o₁ + 8 ≤ o₂) :
    (a.setUInt64BE! o₁ v).getUInt64BE! o₂ = a.getUInt64BE! o₂ := by
  unfold getUInt64BE!
  simp only [size_setUInt64BE!, get!_eq_getElem!]
  rw [if_pos h₂, if_pos h₂,
      getElem!_setUInt64BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64BE!_of_outside _ _ _ _ (by omega),
      getElem!_setUInt64BE!_of_outside _ _ _ _ (by omega)]

end ByteArray
