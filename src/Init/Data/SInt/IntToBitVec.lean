/-
Copyright (c) 2026 Lean FRO LLC or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
module

prelude
public import Init.Data.SInt.Lemmas
public import Init.Data.SInt.Bitwise
public import Init.Data.UInt.IntToBitVec

public section

theorem ISize.toBitVec32_eq_toBitVec (a : ISize) (h : System.Platform.numBits = 32) :
    a.toBitVec32 h = a.toBitVec.cast h := rfl

theorem ISize.toBitVec64_eq_toBitVec (a : ISize) (h : System.Platform.numBits = 64) :
    a.toBitVec64 h = a.toBitVec.cast h := rfl

/-! ## `numBits = 32` -/

@[int_toBitVec]
theorem ISize.le_iff_toBitVec32_sle {a b : ISize} (h : System.Platform.numBits = 32) :
    a ≤ b ↔ (a.toBitVec32 h).sle (b.toBitVec32 h) := by
  simp only [ISize.le_iff_toBitVec_sle, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.lt_iff_toBitVec32_slt {a b : ISize} (h : System.Platform.numBits = 32) :
    a < b ↔ (a.toBitVec32 h).slt (b.toBitVec32 h) := by
  simp only [ISize.lt_iff_toBitVec_slt, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.eq_iff_toBitVec32_eq {a b : ISize} (h : System.Platform.numBits = 32) :
    a = b ↔ a.toBitVec32 h = b.toBitVec32 h := by
  simp only [ISize.eq_iff_toBitVec_eq, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.ne_iff_toBitVec32_ne {a b : ISize} (h : System.Platform.numBits = 32) :
    a ≠ b ↔ a.toBitVec32 h ≠ b.toBitVec32 h := by
  simp only [ISize.ne_iff_toBitVec_ne, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_ofNat (n : Nat) (h : System.Platform.numBits = 32) :
    toBitVec32 (no_index (OfNat.ofNat n)) h = BitVec.ofNat _ n := by
  simp only [ISize.toBitVec_ofNat, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_ofInt (i : Int) (h : System.Platform.numBits = 32) :
    (ISize.ofInt i).toBitVec32 h = BitVec.ofInt _ i := by
  simp only [ISize.toBitVec_ofInt, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_add {a b : ISize} (h : System.Platform.numBits = 32) :
    (a + b).toBitVec32 h = a.toBitVec32 h + b.toBitVec32 h := by
  simp only [ISize.toBitVec_add, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_sub {a b : ISize} (h : System.Platform.numBits = 32) :
    (a - b).toBitVec32 h = a.toBitVec32 h - b.toBitVec32 h := by
  simp only [ISize.toBitVec_sub, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_mul {a b : ISize} (h : System.Platform.numBits = 32) :
    (a * b).toBitVec32 h = a.toBitVec32 h * b.toBitVec32 h := by
  simp only [ISize.toBitVec_mul, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_div {a b : ISize} (h : System.Platform.numBits = 32) :
    (a / b).toBitVec32 h = (a.toBitVec32 h).sdiv (b.toBitVec32 h) := by
  simp only [ISize.toBitVec_div, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_mod {a b : ISize} (h : System.Platform.numBits = 32) :
    (a % b).toBitVec32 h = (a.toBitVec32 h).srem (b.toBitVec32 h) := by
  simp only [ISize.toBitVec_mod, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_neg {a : ISize} (h : System.Platform.numBits = 32) :
    (-a).toBitVec32 h = -a.toBitVec32 h := by
  simp only [ISize.toBitVec_neg, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_not {a : ISize} (h : System.Platform.numBits = 32) :
    (~~~a).toBitVec32 h = ~~~a.toBitVec32 h := by
  simp only [ISize.toBitVec_not, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_and (a b : ISize) (h : System.Platform.numBits = 32) :
    (a &&& b).toBitVec32 h = a.toBitVec32 h &&& b.toBitVec32 h := by
  simp only [ISize.toBitVec_and, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_or (a b : ISize) (h : System.Platform.numBits = 32) :
    (a ||| b).toBitVec32 h = a.toBitVec32 h ||| b.toBitVec32 h := by
  simp only [ISize.toBitVec_or, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_xor (a b : ISize) (h : System.Platform.numBits = 32) :
    (a ^^^ b).toBitVec32 h = a.toBitVec32 h ^^^ b.toBitVec32 h := by
  simp only [ISize.toBitVec_xor, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_shiftLeft (a b : ISize) (h : System.Platform.numBits = 32) :
    (a <<< b).toBitVec32 h = a.toBitVec32 h <<< ((b.toBitVec32 h).smod 32) := by
  simp only [toBitVec32_eq_toBitVec, ISize.toBitVec_shiftLeft, BitVec.natCast_eq_ofNat,
    BitVec.shiftLeft_eq', BitVec.ofNat_eq_ofNat]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_shiftRight (a b : ISize) (h : System.Platform.numBits = 32) :
    (a >>> b).toBitVec32 h = (a.toBitVec32 h).sshiftRight' ((b.toBitVec32 h).smod 32) := by
  simp only [toBitVec32_eq_toBitVec, ISize.toBitVec_shiftRight, BitVec.natCast_eq_ofNat,
    BitVec.sshiftRight_eq', BitVec.ofNat_eq_ofNat]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_abs (a : ISize) (h : System.Platform.numBits = 32) :
    a.abs.toBitVec32 h = (a.toBitVec32 h).abs := by
  simp only [ISize.toBitVec_abs, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_toInt8 (n : ISize) (h : System.Platform.numBits = 32) :
    n.toInt8.toBitVec = (n.toBitVec32 h).signExtend 8 := by
  simp only [ISize.toBitVec_toInt8, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_toInt16 (n : ISize) (h : System.Platform.numBits = 32) :
    n.toInt16.toBitVec = (n.toBitVec32 h).signExtend 16 := by
  simp only [ISize.toBitVec_toInt16, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_toInt32 (n : ISize) (h : System.Platform.numBits = 32) :
    n.toInt32.toBitVec = (n.toBitVec32 h).signExtend 32 := by
  simp only [ISize.toBitVec_toInt32, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_toInt64 (n : ISize) (h : System.Platform.numBits = 32) :
    n.toInt64.toBitVec = (n.toBitVec32 h).signExtend 64 := by
  simp only [ISize.toBitVec_toInt64, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_toUSize (n : ISize) (h : System.Platform.numBits = 32) :
    n.toUSize.toBitVec32 h = n.toBitVec32 h := by
  simp only [ISize.toBitVec_toUSize, USize.toBitVec32_eq_toBitVec, ISize.toBitVec32_eq_toBitVec]

@[int_toBitVec]
theorem USize.toBitVec32_toISize (n : USize) (h : System.Platform.numBits = 32) :
    n.toISize.toBitVec32 h = n.toBitVec32 h := by
  simp only [USize.toBitVec_toISize, USize.toBitVec32_eq_toBitVec, ISize.toBitVec32_eq_toBitVec]

@[int_toBitVec]
theorem Int8.toBitVec32_toISize (n : Int8) (h : System.Platform.numBits = 32) :
    n.toISize.toBitVec32 h = n.toBitVec.signExtend 32 := by
  simp only [Int8.toBitVec_toISize, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Int16.toBitVec32_toISize (n : Int16) (h : System.Platform.numBits = 32) :
    n.toISize.toBitVec32 h = n.toBitVec.signExtend 32 := by
  simp only [Int16.toBitVec_toISize, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Int32.toBitVec32_toISize (n : Int32) (h : System.Platform.numBits = 32) :
    n.toISize.toBitVec32 h = n.toBitVec.signExtend 32 := by
  simp only [Int32.toBitVec_toISize, ISize.toBitVec32_eq_toBitVec]
  generalize System.Platform.numBits = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Int64.toBitVec32_toISize (n : Int64) (h : System.Platform.numBits = 32) :
    n.toISize.toBitVec32 h = n.toBitVec.signExtend 32 := by
  simp only [Int64.toBitVec_toISize, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_ofBitVec (n) (h : System.Platform.numBits = 32) :
    (ISize.ofBitVec n).toBitVec32 h = n.cast h := by
  simp only [ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_minValue (h : System.Platform.numBits = 32) :
    ISize.minValue.toBitVec32 h = BitVec.intMin 32 := by
  simp only [ISize.toBitVec_minValue, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec32_maxValue (h : System.Platform.numBits = 32) :
    ISize.maxValue.toBitVec32 h = BitVec.intMax 32 := by
  simp only [ISize.toBitVec_maxValue, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Bool.toBitVec32_toISize {b : Bool} (h : System.Platform.numBits = 32) :
    b.toISize.toBitVec32 h = (BitVec.ofBool b).setWidth 32 := by
  simp only [Bool.toBitVec_toISize, ISize.toBitVec32_eq_toBitVec]
  generalize 32 = x at *
  subst h
  rfl

/-! ## `numBits = 64` -/

@[int_toBitVec]
theorem ISize.le_iff_toBitVec64_sle {a b : ISize} (h : System.Platform.numBits = 64) :
    a ≤ b ↔ (a.toBitVec64 h).sle (b.toBitVec64 h) := by
  simp only [ISize.le_iff_toBitVec_sle, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.lt_iff_toBitVec64_slt {a b : ISize} (h : System.Platform.numBits = 64) :
    a < b ↔ (a.toBitVec64 h).slt (b.toBitVec64 h) := by
  simp only [ISize.lt_iff_toBitVec_slt, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.eq_iff_toBitVec64_eq {a b : ISize} (h : System.Platform.numBits = 64) :
    a = b ↔ a.toBitVec64 h = b.toBitVec64 h := by
  simp only [ISize.eq_iff_toBitVec_eq, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.ne_iff_toBitVec64_ne {a b : ISize} (h : System.Platform.numBits = 64) :
    a ≠ b ↔ a.toBitVec64 h ≠ b.toBitVec64 h := by
  simp only [ISize.ne_iff_toBitVec_ne, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_ofNat (n : Nat) (h : System.Platform.numBits = 64) :
    toBitVec64 (no_index (OfNat.ofNat n)) h = BitVec.ofNat _ n := by
  simp only [ISize.toBitVec_ofNat, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_ofInt (i : Int) (h : System.Platform.numBits = 64) :
    (ISize.ofInt i).toBitVec64 h = BitVec.ofInt _ i := by
  simp only [ISize.toBitVec_ofInt, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_add {a b : ISize} (h : System.Platform.numBits = 64) :
    (a + b).toBitVec64 h = a.toBitVec64 h + b.toBitVec64 h := by
  simp only [ISize.toBitVec_add, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_sub {a b : ISize} (h : System.Platform.numBits = 64) :
    (a - b).toBitVec64 h = a.toBitVec64 h - b.toBitVec64 h := by
  simp only [ISize.toBitVec_sub, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_mul {a b : ISize} (h : System.Platform.numBits = 64) :
    (a * b).toBitVec64 h = a.toBitVec64 h * b.toBitVec64 h := by
  simp only [ISize.toBitVec_mul, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_div {a b : ISize} (h : System.Platform.numBits = 64) :
    (a / b).toBitVec64 h = (a.toBitVec64 h).sdiv (b.toBitVec64 h) := by
  simp only [ISize.toBitVec_div, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_mod {a b : ISize} (h : System.Platform.numBits = 64) :
    (a % b).toBitVec64 h = (a.toBitVec64 h).srem (b.toBitVec64 h) := by
  simp only [ISize.toBitVec_mod, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_neg {a : ISize} (h : System.Platform.numBits = 64) :
    (-a).toBitVec64 h = -a.toBitVec64 h := by
  simp only [ISize.toBitVec_neg, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_not {a : ISize} (h : System.Platform.numBits = 64) :
    (~~~a).toBitVec64 h = ~~~a.toBitVec64 h := by
  simp only [ISize.toBitVec_not, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_and (a b : ISize) (h : System.Platform.numBits = 64) :
    (a &&& b).toBitVec64 h = a.toBitVec64 h &&& b.toBitVec64 h := by
  simp only [ISize.toBitVec_and, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_or (a b : ISize) (h : System.Platform.numBits = 64) :
    (a ||| b).toBitVec64 h = a.toBitVec64 h ||| b.toBitVec64 h := by
  simp only [ISize.toBitVec_or, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_xor (a b : ISize) (h : System.Platform.numBits = 64) :
    (a ^^^ b).toBitVec64 h = a.toBitVec64 h ^^^ b.toBitVec64 h := by
  simp only [ISize.toBitVec_xor, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_shiftLeft (a b : ISize) (h : System.Platform.numBits = 64) :
    (a <<< b).toBitVec64 h = a.toBitVec64 h <<< ((b.toBitVec64 h).smod 64) := by
  simp only [toBitVec64_eq_toBitVec, ISize.toBitVec_shiftLeft, BitVec.natCast_eq_ofNat,
    BitVec.shiftLeft_eq', BitVec.ofNat_eq_ofNat]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_shiftRight (a b : ISize) (h : System.Platform.numBits = 64) :
    (a >>> b).toBitVec64 h = (a.toBitVec64 h).sshiftRight' ((b.toBitVec64 h).smod 64) := by
  simp only [toBitVec64_eq_toBitVec, ISize.toBitVec_shiftRight, BitVec.natCast_eq_ofNat,
    BitVec.sshiftRight_eq', BitVec.ofNat_eq_ofNat]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_abs (a : ISize) (h : System.Platform.numBits = 64) :
    a.abs.toBitVec64 h = (a.toBitVec64 h).abs := by
  simp only [ISize.toBitVec_abs, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_toInt8 (n : ISize) (h : System.Platform.numBits = 64) :
    n.toInt8.toBitVec = (n.toBitVec64 h).signExtend 8 := by
  simp only [ISize.toBitVec_toInt8, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_toInt16 (n : ISize) (h : System.Platform.numBits = 64) :
    n.toInt16.toBitVec = (n.toBitVec64 h).signExtend 16 := by
  simp only [ISize.toBitVec_toInt16, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_toInt32 (n : ISize) (h : System.Platform.numBits = 64) :
    n.toInt32.toBitVec = (n.toBitVec64 h).signExtend 32 := by
  simp only [ISize.toBitVec_toInt32, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_toInt64 (n : ISize) (h : System.Platform.numBits = 64) :
    n.toInt64.toBitVec = (n.toBitVec64 h).signExtend 64 := by
  simp only [ISize.toBitVec_toInt64, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_toUSize (n : ISize) (h : System.Platform.numBits = 64) :
    n.toUSize.toBitVec64 h = n.toBitVec64 h := by
  simp only [ISize.toBitVec_toUSize, USize.toBitVec64_eq_toBitVec, ISize.toBitVec64_eq_toBitVec]

@[int_toBitVec]
theorem USize.toBitVec64_toISize (n : USize) (h : System.Platform.numBits = 64) :
    n.toISize.toBitVec64 h = n.toBitVec64 h := by
  simp only [USize.toBitVec_toISize, USize.toBitVec64_eq_toBitVec, ISize.toBitVec64_eq_toBitVec]

@[int_toBitVec]
theorem Int8.toBitVec64_toISize (n : Int8) (h : System.Platform.numBits = 64) :
    n.toISize.toBitVec64 h = n.toBitVec.signExtend 64 := by
  simp only [Int8.toBitVec_toISize, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Int16.toBitVec64_toISize (n : Int16) (h : System.Platform.numBits = 64) :
    n.toISize.toBitVec64 h = n.toBitVec.signExtend 64 := by
  simp only [Int16.toBitVec_toISize, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Int32.toBitVec64_toISize (n : Int32) (h : System.Platform.numBits = 64) :
    n.toISize.toBitVec64 h = n.toBitVec.signExtend 64 := by
  simp only [Int32.toBitVec_toISize, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Int64.toBitVec64_toISize (n : Int64) (h : System.Platform.numBits = 64) :
    n.toISize.toBitVec64 h = n.toBitVec.signExtend 64 := by
  simp only [Int64.toBitVec_toISize, ISize.toBitVec64_eq_toBitVec]
  generalize System.Platform.numBits = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_ofBitVec (n) (h : System.Platform.numBits = 64) :
    (ISize.ofBitVec n).toBitVec64 h = n.cast h := by
  simp only [ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_minValue (h : System.Platform.numBits = 64) :
    ISize.minValue.toBitVec64 h = BitVec.intMin 64 := by
  simp only [ISize.toBitVec_minValue, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem ISize.toBitVec64_maxValue (h : System.Platform.numBits = 64) :
    ISize.maxValue.toBitVec64 h = BitVec.intMax 64 := by
  simp only [ISize.toBitVec_maxValue, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl

@[int_toBitVec]
theorem Bool.toBitVec64_toISize {b : Bool} (h : System.Platform.numBits = 64) :
    b.toISize.toBitVec64 h = (BitVec.ofBool b).setWidth 64 := by
  simp only [Bool.toBitVec_toISize, ISize.toBitVec64_eq_toBitVec]
  generalize 64 = x at *
  subst h
  rfl
