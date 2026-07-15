/-
Copyright (c) 2026 Lean FRO LLC or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.UInt.Lemmas
public import Init.Data.UInt.Bitwise

public section

theorem USize.toBitVec32_eq_toBitVec (a : USize) (h : System.Platform.numBits = 32) :
    a.toBitVec32 h = a.toBitVec.cast h := rfl

theorem USize.toBitVec64_eq_toBitVec (a : USize) (h : System.Platform.numBits = 64) :
    a.toBitVec64 h = a.toBitVec.cast h := rfl

/-! ## `numBits = 32` -/

@[int_toBitVec]
theorem USize.le_iff_toBitVec32_le {a b : USize} (h : System.Platform.numBits = 32) :
    a ≤ b ↔ a.toBitVec32 h ≤ b.toBitVec32 h := by
  simp only [USize.le_iff_toBitVec_le, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.lt_iff_toBitVec32_lt {a b : USize} (h : System.Platform.numBits = 32) :
    a < b ↔ a.toBitVec32 h < b.toBitVec32 h := by
  simp only [USize.lt_iff_toBitVec_lt, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.eq_iff_toBitVec32_eq {a b : USize} (h : System.Platform.numBits = 32) :
    a = b ↔ a.toBitVec32 h = b.toBitVec32 h := by
  simp only [USize.eq_iff_toBitVec_eq, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.ne_iff_toBitVec32_ne {a b : USize} (h : System.Platform.numBits = 32) :
    a ≠ b ↔ a.toBitVec32 h ≠ b.toBitVec32 h := by
  simp only [USize.ne_iff_toBitVec_ne, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_ofNat (n : Nat) (h : System.Platform.numBits = 32) :
    toBitVec32 (no_index (OfNat.ofNat n)) h = BitVec.ofNat _ n := by
  simp only [USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_add {a b : USize} (h : System.Platform.numBits = 32) :
    (a + b).toBitVec32 h = a.toBitVec32 h + b.toBitVec32 h := by
  simp only [USize.toBitVec_add, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_sub {a b : USize} (h : System.Platform.numBits = 32) :
    (a - b).toBitVec32 h = a.toBitVec32 h - b.toBitVec32 h := by
  simp only [USize.toBitVec_sub, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_mul {a b : USize} (h : System.Platform.numBits = 32) :
    (a * b).toBitVec32 h = a.toBitVec32 h * b.toBitVec32 h := by
  simp only [USize.toBitVec_mul, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_div {a b : USize} (h : System.Platform.numBits = 32) :
    (a / b).toBitVec32 h = a.toBitVec32 h / b.toBitVec32 h := by
  simp only [USize.toBitVec_div, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_mod {a b : USize} (h : System.Platform.numBits = 32) :
    (a % b).toBitVec32 h = a.toBitVec32 h % b.toBitVec32 h := by
  simp only [USize.toBitVec_mod, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_neg {a : USize} (h : System.Platform.numBits = 32) :
    (-a).toBitVec32 h = -a.toBitVec32 h := by
  simp only [USize.toBitVec_neg, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_not {a : USize} (h : System.Platform.numBits = 32) :
    (~~~a).toBitVec32 h = ~~~a.toBitVec32 h := by
  simp only [USize.toBitVec_not, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_and (a b : USize) (h : System.Platform.numBits = 32) :
    (a &&& b).toBitVec32 h = a.toBitVec32 h &&& b.toBitVec32 h := by
  simp only [USize.toBitVec_and, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_or (a b : USize) (h : System.Platform.numBits = 32) :
    (a ||| b).toBitVec32 h = a.toBitVec32 h ||| b.toBitVec32 h := by
  simp only [USize.toBitVec_or, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_xor (a b : USize) (h : System.Platform.numBits = 32) :
    (a ^^^ b).toBitVec32 h = a.toBitVec32 h ^^^ b.toBitVec32 h := by
  simp only [USize.toBitVec_xor, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_shiftLeft (a b : USize) (h : System.Platform.numBits = 32) :
    (a <<< b).toBitVec32 h = a.toBitVec32 h <<< (b.toBitVec32 h % 32) := by
  simp only [toBitVec32_eq_toBitVec, USize.toBitVec_shiftLeft, BitVec.natCast_eq_ofNat,
    BitVec.ofNat_eq_ofNat]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_shiftRight (a b : USize) (h : System.Platform.numBits = 32) :
    (a >>> b).toBitVec32 h = a.toBitVec32 h >>> (b.toBitVec32 h % 32) := by
  simp only [toBitVec32_eq_toBitVec, USize.toBitVec_shiftRight, BitVec.natCast_eq_ofNat,
    BitVec.ofNat_eq_ofNat]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_toUInt8 (n : USize) (h : System.Platform.numBits = 32) :
    n.toUInt8.toBitVec = (n.toBitVec32 h).setWidth 8 := by
  simp only [USize.toBitVec_toUInt8, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_toUInt16 (n : USize) (h : System.Platform.numBits = 32) :
    n.toUInt16.toBitVec = (n.toBitVec32 h).setWidth 16 := by
  simp only [USize.toBitVec_toUInt16, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_toUInt32 (n : USize) (h : System.Platform.numBits = 32) :
    n.toUInt32.toBitVec = (n.toBitVec32 h).setWidth 32 := by
  simp only [USize.toBitVec_toUInt32, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_toUInt64 (n : USize) (h : System.Platform.numBits = 32) :
    n.toUInt64.toBitVec = (n.toBitVec32 h).setWidth 64 := by
  simp only [USize.toBitVec_toUInt64, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem UInt8.toBitVec32_toUSize (n : UInt8) (h : System.Platform.numBits = 32) :
    n.toUSize.toBitVec32 h = n.toBitVec.setWidth 32 := by
  simp only [UInt8.toBitVec_toUSize, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem UInt16.toBitVec32_toUSize (n : UInt16) (h : System.Platform.numBits = 32) :
    n.toUSize.toBitVec32 h = n.toBitVec.setWidth 32 := by
  simp only [UInt16.toBitVec_toUSize, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem UInt32.toBitVec32_toUSize (n : UInt32) (h : System.Platform.numBits = 32) :
    n.toUSize.toBitVec32 h = n.toBitVec := by
  simp only [UInt32.toBitVec_toUSize, USize.toBitVec32_eq_toBitVec]
  generalize System.Platform.numBits = x at *
  subst h
  rfl

@[int_toBitVec]
theorem UInt64.toBitVec32_toUSize (n : UInt64) (h : System.Platform.numBits = 32) :
    n.toUSize.toBitVec32 h = n.toBitVec.setWidth 32 := by
  simp only [UInt64.toBitVec_toUSize, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_ofNatLT {n : Nat} (hn : n < USize.size) (h : System.Platform.numBits = 32) :
    (USize.ofNatLT n hn).toBitVec32 h = BitVec.ofNatLT n (h ▸ hn) := by
  simp only [USize.toBitVec_ofNatLT, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_ofFin (n : Fin USize.size) (h : System.Platform.numBits = 32) :
    (USize.ofFin n).toBitVec32 h = BitVec.ofFin (h ▸ n) := by
  simp only [USize.toBitVec_ofFin, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec32_ofBitVec (n) (h : System.Platform.numBits = 32) :
    (USize.ofBitVec n).toBitVec32 h = n.cast h := by
  simp only [USize.toBitVec32_eq_toBitVec]

@[int_toBitVec]
theorem USize.toBitVec32_pow (a : USize) (n : Nat) (h : System.Platform.numBits = 32) :
    (a ^ n).toBitVec32 h = a.toBitVec32 h ^ n := by
  simp only [USize.toBitVec_pow, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Bool.toBitVec32_toUSize {b : Bool} (h : System.Platform.numBits = 32) :
    b.toUSize.toBitVec32 h = (BitVec.ofBool b).setWidth 32 := by
  simp only [Bool.toBitVec_toUSize, USize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

/-! ## `numBits = 64` -/

@[int_toBitVec]
theorem USize.le_iff_toBitVec64_le {a b : USize} (h : System.Platform.numBits = 64) :
    a ≤ b ↔ a.toBitVec64 h ≤ b.toBitVec64 h := by
  simp only [USize.le_iff_toBitVec_le, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.lt_iff_toBitVec64_lt {a b : USize} (h : System.Platform.numBits = 64) :
    a < b ↔ a.toBitVec64 h < b.toBitVec64 h := by
  simp only [USize.lt_iff_toBitVec_lt, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.eq_iff_toBitVec64_eq {a b : USize} (h : System.Platform.numBits = 64) :
    a = b ↔ a.toBitVec64 h = b.toBitVec64 h := by
  simp only [USize.eq_iff_toBitVec_eq, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.ne_iff_toBitVec64_ne {a b : USize} (h : System.Platform.numBits = 64) :
    a ≠ b ↔ a.toBitVec64 h ≠ b.toBitVec64 h := by
  simp only [USize.ne_iff_toBitVec_ne, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_ofNat (n : Nat) (h : System.Platform.numBits = 64) :
    toBitVec64 (no_index (OfNat.ofNat n)) h = BitVec.ofNat _ n := by
  simp only [USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_add {a b : USize} (h : System.Platform.numBits = 64) :
    (a + b).toBitVec64 h = a.toBitVec64 h + b.toBitVec64 h := by
  simp only [USize.toBitVec_add, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_sub {a b : USize} (h : System.Platform.numBits = 64) :
    (a - b).toBitVec64 h = a.toBitVec64 h - b.toBitVec64 h := by
  simp only [USize.toBitVec_sub, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_mul {a b : USize} (h : System.Platform.numBits = 64) :
    (a * b).toBitVec64 h = a.toBitVec64 h * b.toBitVec64 h := by
  simp only [USize.toBitVec_mul, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_div {a b : USize} (h : System.Platform.numBits = 64) :
    (a / b).toBitVec64 h = a.toBitVec64 h / b.toBitVec64 h := by
  simp only [USize.toBitVec_div, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_mod {a b : USize} (h : System.Platform.numBits = 64) :
    (a % b).toBitVec64 h = a.toBitVec64 h % b.toBitVec64 h := by
  simp only [USize.toBitVec_mod, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_neg {a : USize} (h : System.Platform.numBits = 64) :
    (-a).toBitVec64 h = -a.toBitVec64 h := by
  simp only [USize.toBitVec_neg, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_not {a : USize} (h : System.Platform.numBits = 64) :
    (~~~a).toBitVec64 h = ~~~a.toBitVec64 h := by
  simp only [USize.toBitVec_not, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_and (a b : USize) (h : System.Platform.numBits = 64) :
    (a &&& b).toBitVec64 h = a.toBitVec64 h &&& b.toBitVec64 h := by
  simp only [USize.toBitVec_and, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_or (a b : USize) (h : System.Platform.numBits = 64) :
    (a ||| b).toBitVec64 h = a.toBitVec64 h ||| b.toBitVec64 h := by
  simp only [USize.toBitVec_or, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_xor (a b : USize) (h : System.Platform.numBits = 64) :
    (a ^^^ b).toBitVec64 h = a.toBitVec64 h ^^^ b.toBitVec64 h := by
  simp only [USize.toBitVec_xor, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_shiftLeft (a b : USize) (h : System.Platform.numBits = 64) :
    (a <<< b).toBitVec64 h = a.toBitVec64 h <<< (b.toBitVec64 h % 64) := by
  simp only [toBitVec64_eq_toBitVec, USize.toBitVec_shiftLeft, BitVec.natCast_eq_ofNat,
    BitVec.ofNat_eq_ofNat]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_shiftRight (a b : USize) (h : System.Platform.numBits = 64) :
    (a >>> b).toBitVec64 h = a.toBitVec64 h >>> (b.toBitVec64 h % 64) := by
  simp only [toBitVec64_eq_toBitVec, USize.toBitVec_shiftRight, BitVec.natCast_eq_ofNat,
    BitVec.ofNat_eq_ofNat]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_toUInt8 (n : USize) (h : System.Platform.numBits = 64) :
    n.toUInt8.toBitVec = (n.toBitVec64 h).setWidth 8 := by
  simp only [USize.toBitVec_toUInt8, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_toUInt16 (n : USize) (h : System.Platform.numBits = 64) :
    n.toUInt16.toBitVec = (n.toBitVec64 h).setWidth 16 := by
  simp only [USize.toBitVec_toUInt16, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_toUInt32 (n : USize) (h : System.Platform.numBits = 64) :
    n.toUInt32.toBitVec = (n.toBitVec64 h).setWidth 32 := by
  simp only [USize.toBitVec_toUInt32, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_toUInt64 (n : USize) (h : System.Platform.numBits = 64) :
    n.toUInt64.toBitVec = (n.toBitVec64 h).setWidth 64 := by
  simp only [USize.toBitVec_toUInt64, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem UInt8.toBitVec64_toUSize (n : UInt8) (h : System.Platform.numBits = 64) :
    n.toUSize.toBitVec64 h = n.toBitVec.setWidth 64 := by
  simp only [UInt8.toBitVec_toUSize, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem UInt16.toBitVec64_toUSize (n : UInt16) (h : System.Platform.numBits = 64) :
    n.toUSize.toBitVec64 h = n.toBitVec.setWidth 64 := by
  simp only [UInt16.toBitVec_toUSize, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem UInt32.toBitVec64_toUSize (n : UInt32) (h : System.Platform.numBits = 64) :
    n.toUSize.toBitVec64 h = n.toBitVec.setWidth 64 := by
  simp only [UInt32.toBitVec_toUSize, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem UInt64.toBitVec64_toUSize (n : UInt64) (h : System.Platform.numBits = 64) :
    n.toUSize.toBitVec64 h = n.toBitVec := by
  simp only [UInt64.toBitVec_toUSize, USize.toBitVec64_eq_toBitVec]
  generalize System.Platform.numBits = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_ofNatLT {n : Nat} (hn : n < USize.size) (h : System.Platform.numBits = 64) :
    (USize.ofNatLT n hn).toBitVec64 h = BitVec.ofNatLT n (h ▸ hn) := by
  simp only [USize.toBitVec_ofNatLT, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_ofFin (n : Fin USize.size) (h : System.Platform.numBits = 64) :
    (USize.ofFin n).toBitVec64 h = BitVec.ofFin (h ▸ n) := by
  simp only [USize.toBitVec_ofFin, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem USize.toBitVec64_ofBitVec (n) (h : System.Platform.numBits = 64) :
    (USize.ofBitVec n).toBitVec64 h = n.cast h := by
  simp only [USize.toBitVec64_eq_toBitVec]

@[int_toBitVec]
theorem USize.toBitVec64_pow (a : USize) (n : Nat) (h : System.Platform.numBits = 64) :
    (a ^ n).toBitVec64 h = a.toBitVec64 h ^ n := by
  simp only [USize.toBitVec_pow, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Bool.toBitVec64_toUSize {b : Bool} (h : System.Platform.numBits = 64) :
    b.toUSize.toBitVec64 h = (BitVec.ofBool b).setWidth 64 := by
  simp only [Bool.toBitVec_toUSize, USize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl
