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

private def Int8.toUInt8Mono (a : Int8) : UInt8 :=
  UInt8.ofInt (a.toInt - Int8.minValue.toInt)

private def UInt8.toInt8Mono (a : UInt8) : Int8 :=
  Int8.ofInt (↑a.toNat + Int8.minValue.toInt)

@[simp]
private theorem toInt8Mono_toUInt8Mono {a : Int8} :
    a.toUInt8Mono.toInt8Mono = a := by
  sorry

@[simp]
private theorem toUInt8Mono_toInt8Mono {a : UInt8} :
    a.toInt8Mono.toUInt8Mono = a := by
  sorry

private theorem toInt_toInt8Mono {a : UInt8} :
    a.toInt8Mono.toInt = (↑a.toNat : Int) + Int8.minValue.toInt := by
  sorry

@[simp]
private theorem toInt8Mono_add_one {a : UInt8} :
    a.toInt8Mono + 1 = (a + 1).toInt8Mono := by
  sorry

private theorem toInt8Mono_add {a : UInt8} {k : Nat}
    (h : a.toInt8Mono.toInt + ↑k ≤ Int8.maxValue.toInt) :
    (a + (UInt8.ofNat k)).toInt8Mono = a.toInt8Mono + (Int8.ofInt ↑k) := by
  sorry

namespace Int8

instance : UpwardEnumerable Int8 where
  succ? i := if i + 1 = Int8.minValue then none else some (i + 1)
  succMany? n i :=
    have := i.minValue_le_toInt
    if h : i.toInt + n ≤ Int8.maxValue.toInt then some (.ofIntLE _ (by omega) h) else none

private theorem succ?_toInt8Mono {x : UInt8} :
    UpwardEnumerable.succ? x.toInt8Mono = UInt8.toInt8Mono <$> UpwardEnumerable.succ? x := by
  simp [succ?]
  split <;> rename_i h
  · rw [if_pos]
    · simp [-Int8.reduceToInt]
    · simp [UInt8.toInt8Mono, ← UInt8.toNat_inj, ← Int8.toInt_inj, ← Int.ofNat_inj,
        Int.natCast_emod, Int.emod_eq_iff, Int.bmod_eq_iff] at h ⊢
      omega
  · simp only [← toInt8Mono_add_one]
    rw [if_neg]
    · simp
    · simp [← Int8.toInt_inj, toInt_toInt8Mono, ← UInt8.toNat_inj, ← Int.ofNat_inj] at h ⊢
      omega

private theorem UInt8.toNat_add_lt {k : Nat} {x : UInt8} :
    x.toNat + k < UInt8.size ↔ x.toInt8Mono.toInt + ↑k ≤ Int8.maxValue.toInt := by
  simp [UInt8.toInt8Mono]
  rw [Int.bmod_eq_of_le]
  · simp only [UInt8.size, Int.reduceNeg, maxValue, Int8.reduceToInt]
    omega
  · simp only [Int.cast_ofNat_Int, Int.reduceDiv, Int.reduceNeg]
    omega
  · simp only [Int.reduceNeg, Int.cast_ofNat_Int, Int.reduceAdd, Int.reduceDiv]
    have := UInt8.toNat_lt x
    omega

private theorem succMany?_toInt8Mono {k : Nat} {x : UInt8} :
    UpwardEnumerable.succMany? k x.toInt8Mono = UInt8.toInt8Mono <$> UpwardEnumerable.succMany? k x := by
  simp [succMany?, UInt8.toNat_add_lt]
  split
  · rw [ofIntLE_add, toInt8Mono_add]
    · simp
    · simp [UInt8.toInt8Mono]
  · rfl

private theorem upwardEnumerableLE_toInt8Mono {x y : UInt8} :
    UpwardEnumerable.LE x.toInt8Mono y.toInt8Mono ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 8} :
    UpwardEnumerable.LT (Int8.ofBitVec x) (Int8.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec]

instance : LawfulUpwardEnumerable Int8 where
  ne_of_lt x y := by
    cases x; cases y
    simpa [upwardEnumerableLT_ofBitVec] using LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by
    cases x
    simpa [succMany?_ofBitVec] using succMany?_zero
  succMany?_succ? n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_succ?, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE Int8 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, Int8.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulOrderLT Int8 := inferInstance
instance : LawfulUpwardEnumerableLT Int8 := inferInstance
instance : LawfulUpwardEnumerableLT Int8 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed Int8 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed Int8 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open Int8 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open Int8 := inferInstance

instance : RangeSize .closed Int8 where
  size bound a := bound.toNat + 1 - a.toNat

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed Int8} {x : BitVec 8} :
    RangeSize.size bound (Int8.ofBitVec x) = RangeSize.size (shape := .closed) bound.toBitVec x := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed Int8 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, Int8.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 8) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    cases x
    simpa [rangeSizeSize_eq_toBitVec, Int8.le_iff_toBitVec_le, succ?_ofBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec 8) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, Int8.le_iff_toBitVec_le, ← Int8.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec 8) _ _ _

instance : RangeSize .open Int8 := RangeSize.openOfClosed
instance : LawfulRangeSize .open Int8 := inferInstance

end Int8

namespace Int16

instance : UpwardEnumerable Int16 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < Int16.size then some (.ofNatLT _ h) else none

theorem succ?_ofBitVec {x : BitVec 16} :
    UpwardEnumerable.succ? (Int16.ofBitVec x) = Int16.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← Int16.toBitVec_inj]
  split <;> simp_all

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 16} :
    UpwardEnumerable.succMany? k (Int16.ofBitVec x) = Int16.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp [succMany?]

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 16} :
    UpwardEnumerable.LE (Int16.ofBitVec x) (Int16.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 16} :
    UpwardEnumerable.LT (Int16.ofBitVec x) (Int16.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec]

instance : LawfulUpwardEnumerable Int16 where
  ne_of_lt x y := by
    cases x; cases y
    simpa [upwardEnumerableLT_ofBitVec] using LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by
    cases x
    simpa [succMany?_ofBitVec] using succMany?_zero
  succMany?_succ? n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_succ?, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE Int16 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, Int16.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulOrderLT Int16 := inferInstance
instance : LawfulUpwardEnumerableLT Int16 := inferInstance
instance : LawfulUpwardEnumerableLT Int16 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed Int16 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed Int16 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open Int16 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open Int16 := inferInstance

instance : RangeSize .closed Int16 where
  size bound a := bound.toNat + 1 - a.toNat

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed Int16} {x : BitVec 16} :
    RangeSize.size bound (Int16.ofBitVec x) = RangeSize.size (shape := .closed) bound.toBitVec x := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed Int16 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, Int16.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 16) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    cases x
    simpa [rangeSizeSize_eq_toBitVec, Int16.le_iff_toBitVec_le, succ?_ofBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec 16) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, Int16.le_iff_toBitVec_le, ← Int16.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec 16) _ _ _

instance : RangeSize .open Int16 := RangeSize.openOfClosed
instance : LawfulRangeSize .open Int16 := inferInstance

end Int16

namespace Int32

instance : UpwardEnumerable Int32 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < Int32.size then some (.ofNatLT _ h) else none

theorem succ?_ofBitVec {x : BitVec 32} :
    UpwardEnumerable.succ? (Int32.ofBitVec x) = Int32.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← Int32.toBitVec_inj]
  split <;> simp_all

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 32} :
    UpwardEnumerable.succMany? k (Int32.ofBitVec x) = Int32.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp [succMany?]

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 32} :
    UpwardEnumerable.LE (Int32.ofBitVec x) (Int32.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 32} :
    UpwardEnumerable.LT (Int32.ofBitVec x) (Int32.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec]

instance : LawfulUpwardEnumerable Int32 where
  ne_of_lt x y := by
    cases x; cases y
    simpa [upwardEnumerableLT_ofBitVec] using LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by
    cases x
    simpa [succMany?_ofBitVec] using succMany?_zero
  succMany?_succ? n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_succ?, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE Int32 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, Int32.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulOrderLT Int32 := inferInstance
instance : LawfulUpwardEnumerableLT Int32 := inferInstance
instance : LawfulUpwardEnumerableLT Int32 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed Int32 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed Int32 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open Int32 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open Int32 := inferInstance

instance : RangeSize .closed Int32 where
  size bound a := bound.toNat + 1 - a.toNat

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed Int32} {x : BitVec 32} :
    RangeSize.size bound (Int32.ofBitVec x) = RangeSize.size (shape := .closed) bound.toBitVec x := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed Int32 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, Int32.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 32) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    cases x
    simpa [rangeSizeSize_eq_toBitVec, Int32.le_iff_toBitVec_le, succ?_ofBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec 32) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, Int32.le_iff_toBitVec_le, ← Int32.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec 32) _ _ _

instance : RangeSize .open Int32 := RangeSize.openOfClosed
instance : LawfulRangeSize .open Int32 := inferInstance

end Int32

namespace Int64

instance : UpwardEnumerable Int64 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < Int64.size then some (.ofNatLT _ h) else none

theorem succ?_ofBitVec {x : BitVec 64} :
    UpwardEnumerable.succ? (Int64.ofBitVec x) = Int64.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← Int64.toBitVec_inj]
  split <;> simp_all

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 64} :
    UpwardEnumerable.succMany? k (Int64.ofBitVec x) = Int64.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp [succMany?]

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 64} :
    UpwardEnumerable.LE (Int64.ofBitVec x) (Int64.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 64} :
    UpwardEnumerable.LT (Int64.ofBitVec x) (Int64.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec]

instance : LawfulUpwardEnumerable Int64 where
  ne_of_lt x y := by
    cases x; cases y
    simpa [upwardEnumerableLT_ofBitVec] using LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by
    cases x
    simpa [succMany?_ofBitVec] using succMany?_zero
  succMany?_succ? n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_succ?, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE Int64 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, Int64.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulOrderLT Int64 := inferInstance
instance : LawfulUpwardEnumerableLT Int64 := inferInstance
instance : LawfulUpwardEnumerableLT Int64 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed Int64 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed Int64 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open Int64 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open Int64 := inferInstance

instance : RangeSize .closed Int64 where
  size bound a := bound.toNat + 1 - a.toNat

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed Int64} {x : BitVec 64} :
    RangeSize.size bound (Int64.ofBitVec x) = RangeSize.size (shape := .closed) bound.toBitVec x := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed Int64 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, Int64.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 64) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    cases x
    simpa [rangeSizeSize_eq_toBitVec, Int64.le_iff_toBitVec_le, succ?_ofBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec 64) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, Int64.le_iff_toBitVec_le, ← Int64.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec 64) _ _ _

instance : RangeSize .open Int64 := RangeSize.openOfClosed
instance : LawfulRangeSize .open Int64 := inferInstance

end Int64

namespace USize

instance : UpwardEnumerable USize where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < USize.size then some (.ofNatLT _ h) else none

theorem succ?_ofBitVec {x : BitVec System.Platform.numBits} :
    UpwardEnumerable.succ? (USize.ofBitVec x) = USize.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← USize.toBitVec_inj]
  split <;> simp_all

theorem succMany?_ofBitVec {k : Nat} {x : BitVec System.Platform.numBits} :
    UpwardEnumerable.succMany? k (USize.ofBitVec x) = USize.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp [succMany?]

theorem upwardEnumerableLE_ofBitVec {x y : BitVec System.Platform.numBits} :
    UpwardEnumerable.LE (USize.ofBitVec x) (USize.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec System.Platform.numBits} :
    UpwardEnumerable.LT (USize.ofBitVec x) (USize.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec]

instance : LawfulUpwardEnumerable USize where
  ne_of_lt x y := by
    cases x; cases y
    simpa [upwardEnumerableLT_ofBitVec] using LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by
    cases x
    simpa [succMany?_ofBitVec] using succMany?_zero
  succMany?_succ? n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_succ?, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE USize where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, USize.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulOrderLT USize := inferInstance
instance : LawfulUpwardEnumerableLT USize := inferInstance
instance : LawfulUpwardEnumerableLT USize := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed USize := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed USize := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open USize := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open USize := inferInstance

instance : RangeSize .closed USize where
  size bound a := bound.toNat + 1 - a.toNat

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed USize} {x : BitVec System.Platform.numBits} :
    RangeSize.size bound (USize.ofBitVec x) = RangeSize.size (shape := .closed) bound.toBitVec x := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed USize where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, USize.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec System.Platform.numBits) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    cases x
    simpa [rangeSizeSize_eq_toBitVec, USize.le_iff_toBitVec_le, succ?_ofBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec System.Platform.numBits) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, USize.le_iff_toBitVec_le, ← USize.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec System.Platform.numBits) _ _ _

instance : RangeSize .open USize := RangeSize.openOfClosed
instance : LawfulRangeSize .open USize := inferInstance

end USize
