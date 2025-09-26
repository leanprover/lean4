/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Order.Lemmas
public import Init.Data.SInt
import Init.Omega
public import Init.Data.Range.Polymorphic.BitVec
import Init.Data.Range.Polymorphic.UInt

public section

open Std Std.PRange

namespace Int8

open BitVec.Signed

attribute [-instance] BitVec.instUpwardEnumerable BitVec.instHasSize BitVec.instHasSize_1
  BitVec.instHasSize_2 BitVec.instLawfulUpwardEnumerable

instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = Int8.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int8.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

theorem succ?_ofBitVec {x : BitVec 8} :
    UpwardEnumerable.succ? (Int8.ofBitVec x) = Int8.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, ← toBitVec_inj, Int8.toBitVec_add, toBitVec_ofBitVec, toBitVec_ofNat,
    BitVec.ofNat_eq_ofNat, toBitVec_neg, BitVec.reduceNeg, rotate, BitVec.natCast_eq_ofNat,
    Option.map_eq_map, Option.map_map, Function.comp_def]
  split <;> split <;> try (simp_all [Int8.add_assoc]; done)
  all_goals
    rename_i h h'
    rw [BitVec.add_assoc, BitVec.add_comm 128#8 1#8, ← BitVec.add_assoc,
      ← BitVec.eq_sub_iff_add_eq] at h'
    simp [h] at h'

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 8} :
    UpwardEnumerable.succMany? k (Int8.ofBitVec x) =
      Int8.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp only [succMany?, maxValue, ofIntLE_eq_ofInt, ofInt_add, dite_eq_ite, rotate,
    BitVec.ofNatLT_eq_ofNat, Option.map_eq_map, Option.map_if, ofBitVec_add, ofBitVec_ofNat,
    ofNat_add, ofNat_bitVecToNat]
  split <;> split <;> try (simp [← ofBitVec_ofInt, Int8.add_assoc, Int8.add_comm (-128)]; done)
  all_goals
    rename_i h h'
    simp [toInt_eq_ofNat_toNat_rotate_sub, rotate] at h h'
    omega

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 8} :
    UpwardEnumerable.LE (Int8.ofBitVec x) (Int8.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec, ofBitVec_inj]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 8} :
    UpwardEnumerable.LT (Int8.ofBitVec x) (Int8.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec, ofBitVec_inj]

instance : LawfulUpwardEnumerable Int8 where
  ne_of_lt x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLT_ofBitVec, ne_iff_ofBitVec_ne, -ofBitVec_toBitVec] using
      LawfulUpwardEnumerable.ne_of_lt (α := BitVec 8) _ _
  succMany?_zero x := by
    rw [← ofBitVec_toBitVec x]
    simpa [succMany?_ofBitVec, ofBitVec_inj, -ofBitVec_toBitVec] using succMany?_zero
  succMany?_add_one n x := by
    rw [← ofBitVec_toBitVec x]
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec, -ofBitVec_toBitVec]

private theorem toBitVec_le {x y : Int8} :
    x.toBitVec ≤ y.toBitVec ↔ x ≤ y := by
  rw [Int8.le_iff_toBitVec_sle]
  simp [LE.le]

private theorem ofBitVec_le {x y : BitVec 8} :
    Int8.ofBitVec x ≤ Int8.ofBitVec y ↔ x ≤ y := by
  simp [← toBitVec_le]

instance : LawfulUpwardEnumerableLE Int8 where
  le_iff x y := by
    rw [← ofBitVec_toBitVec x, ← ofBitVec_toBitVec y]
    simpa [upwardEnumerableLE_ofBitVec, -ofBitVec_toBitVec, ofBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff (α := BitVec 8) _ _

instance : LawfulUpwardEnumerableLT Int8 := inferInstance
instance : LawfulUpwardEnumerableLT Int8 := inferInstance

instance : Rxc.HasSize Int8 where
  size lo hi := (hi.toInt + 1 - lo.toInt).toNat

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (Int8.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  simp [Rxc.HasSize.size, rotate, ← toInt_toBitVec, toInt_eq_ofNat_toNat_rotate_sub]
  omega

private theorem ofBitVec_eq_iff {x : BitVec 8} {y : Int8} :
    Int8.ofBitVec x = y ↔ x = y.toBitVec := by
  rw [← toBitVec_ofBitVec x, toBitVec_inj, toBitVec_ofBitVec]

instance : Rxc.LawfulHasSize Int8 where
  size_eq_zero_of_not_le lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt8.lt_iff_toBitVec_lt, ofBitVec_le, -ofBitVec_toBitVec] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec 8) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, succ?_ofBitVec, ofBitVec_le,
      -ofBitVec_toBitVec] using Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 8) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec x, ← ofBitVec_toBitVec hi]
    simpa [rxcHasSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, ← UInt8.toBitVec_inj,
      ofBitVec_le, succ?_ofBitVec, -ofBitVec_toBitVec, ofBitVec_eq_iff] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 8) _ _ _

instance : Rxc.IsAlwaysFinite Int8 := inferInstance

instance : Rxo.HasSize Int8 := .ofClosed
instance : Rxo.LawfulHasSize Int8 := inferInstance
instance : Rxo.IsAlwaysFinite Int8 := inferInstance

instance : Rxi.HasSize Int8 where
  size lo := ((2 : Int) ^ 7 - lo.toInt).toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (Int8.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size, rotate, toInt_eq_ofNat_toNat_rotate_sub]
  omega

instance : Rxi.LawfulHasSize Int8 where
  size_eq_one_of_succ?_eq_none lo := by
    rw [← ofBitVec_toBitVec lo]
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 8) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    rw [← ofBitVec_toBitVec lo, ← ofBitVec_toBitVec lo']
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec, ofBitVec_eq_iff, -ofBitVec_toBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 8) _ _

end Int8
