/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.Instances
public import Init.Data.Order.Lemmas
public import Init.Data.UInt
import Init.Omega
public import Init.Data.Range.Polymorphic.BitVec

public section

open Std Std.PRange

namespace UInt8

instance : UpwardEnumerable UInt8 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt8.size then some (.ofNatLT _ h) else none

theorem succ?_ofBitVec {x : BitVec 8} :
    UpwardEnumerable.succ? (UInt8.ofBitVec x) = UInt8.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← UInt8.toBitVec_inj]
  split <;> simp_all

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 8} :
    UpwardEnumerable.succMany? k (UInt8.ofBitVec x) = UInt8.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp [succMany?]

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 8} :
    UpwardEnumerable.LE (UInt8.ofBitVec x) (UInt8.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 8} :
    UpwardEnumerable.LT (UInt8.ofBitVec x) (UInt8.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec]

instance : LawfulUpwardEnumerable UInt8 where
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

instance : LawfulUpwardEnumerableLE UInt8 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, UInt8.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulOrderLT UInt8 := inferInstance
instance : LawfulUpwardEnumerableLT UInt8 := inferInstance
instance : LawfulUpwardEnumerableLT UInt8 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed UInt8 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed UInt8 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open UInt8 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open UInt8 := inferInstance

instance : RangeSize .closed UInt8 where
  size bound a := bound.toNat + 1 - a.toNat

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed UInt8} {x : BitVec 8} :
    RangeSize.size bound (UInt8.ofBitVec x) = RangeSize.size (shape := .closed) bound.toBitVec x := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed UInt8 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt8.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 8) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    cases x
    simpa [rangeSizeSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, succ?_ofBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec 8) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, ← UInt8.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec 8) _ _ _

instance : RangeSize .open UInt8 := RangeSize.openOfClosed
instance : LawfulRangeSize .open UInt8 := inferInstance

end UInt8

namespace UInt16

instance : UpwardEnumerable UInt16 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt16.size then some (.ofNatLT _ h) else none

theorem succ?_ofBitVec {x : BitVec 16} :
    UpwardEnumerable.succ? (UInt16.ofBitVec x) = UInt16.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← UInt16.toBitVec_inj]
  split <;> simp_all

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 16} :
    UpwardEnumerable.succMany? k (UInt16.ofBitVec x) = UInt16.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp [succMany?]

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 16} :
    UpwardEnumerable.LE (UInt16.ofBitVec x) (UInt16.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 16} :
    UpwardEnumerable.LT (UInt16.ofBitVec x) (UInt16.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec]

instance : LawfulUpwardEnumerable UInt16 where
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

instance : LawfulUpwardEnumerableLE UInt16 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, UInt16.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulOrderLT UInt16 := inferInstance
instance : LawfulUpwardEnumerableLT UInt16 := inferInstance
instance : LawfulUpwardEnumerableLT UInt16 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed UInt16 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed UInt16 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open UInt16 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open UInt16 := inferInstance

instance : RangeSize .closed UInt16 where
  size bound a := bound.toNat + 1 - a.toNat

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed UInt16} {x : BitVec 16} :
    RangeSize.size bound (UInt16.ofBitVec x) = RangeSize.size (shape := .closed) bound.toBitVec x := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed UInt16 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt16.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 16) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    cases x
    simpa [rangeSizeSize_eq_toBitVec, UInt16.le_iff_toBitVec_le, succ?_ofBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec 16) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt16.le_iff_toBitVec_le, ← UInt16.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec 16) _ _ _

instance : RangeSize .open UInt16 := RangeSize.openOfClosed
instance : LawfulRangeSize .open UInt16 := inferInstance

end UInt16

namespace UInt32

instance : UpwardEnumerable UInt32 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt32.size then some (.ofNatLT _ h) else none

theorem succ?_ofBitVec {x : BitVec 32} :
    UpwardEnumerable.succ? (UInt32.ofBitVec x) = UInt32.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← UInt32.toBitVec_inj]
  split <;> simp_all

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 32} :
    UpwardEnumerable.succMany? k (UInt32.ofBitVec x) = UInt32.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp [succMany?]

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 32} :
    UpwardEnumerable.LE (UInt32.ofBitVec x) (UInt32.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 32} :
    UpwardEnumerable.LT (UInt32.ofBitVec x) (UInt32.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec]

instance : LawfulUpwardEnumerable UInt32 where
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

instance : LawfulUpwardEnumerableLE UInt32 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, UInt32.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulOrderLT UInt32 := inferInstance
instance : LawfulUpwardEnumerableLT UInt32 := inferInstance
instance : LawfulUpwardEnumerableLT UInt32 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed UInt32 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed UInt32 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open UInt32 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open UInt32 := inferInstance

instance : RangeSize .closed UInt32 where
  size bound a := bound.toNat + 1 - a.toNat

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed UInt32} {x : BitVec 32} :
    RangeSize.size bound (UInt32.ofBitVec x) = RangeSize.size (shape := .closed) bound.toBitVec x := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed UInt32 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt32.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 32) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    cases x
    simpa [rangeSizeSize_eq_toBitVec, UInt32.le_iff_toBitVec_le, succ?_ofBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec 32) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt32.le_iff_toBitVec_le, ← UInt32.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec 32) _ _ _

instance : RangeSize .open UInt32 := RangeSize.openOfClosed
instance : LawfulRangeSize .open UInt32 := inferInstance

end UInt32

namespace UInt64

instance : UpwardEnumerable UInt64 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt64.size then some (.ofNatLT _ h) else none

theorem succ?_ofBitVec {x : BitVec 64} :
    UpwardEnumerable.succ? (UInt64.ofBitVec x) = UInt64.ofBitVec <$> UpwardEnumerable.succ? x := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← UInt64.toBitVec_inj]
  split <;> simp_all

theorem succMany?_ofBitVec {k : Nat} {x : BitVec 64} :
    UpwardEnumerable.succMany? k (UInt64.ofBitVec x) = UInt64.ofBitVec <$> UpwardEnumerable.succMany? k x := by
  simp [succMany?]

theorem upwardEnumerableLE_ofBitVec {x y : BitVec 64} :
    UpwardEnumerable.LE (UInt64.ofBitVec x) (UInt64.ofBitVec y) ↔ UpwardEnumerable.LE x y := by
  simp [UpwardEnumerable.LE, succMany?_ofBitVec]

theorem upwardEnumerableLT_ofBitVec {x y : BitVec 64} :
    UpwardEnumerable.LT (UInt64.ofBitVec x) (UInt64.ofBitVec y) ↔ UpwardEnumerable.LT x y := by
  simp [UpwardEnumerable.LT, succMany?_ofBitVec]

instance : LawfulUpwardEnumerable UInt64 where
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

instance : LawfulUpwardEnumerableLE UInt64 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, UInt64.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulOrderLT UInt64 := inferInstance
instance : LawfulUpwardEnumerableLT UInt64 := inferInstance
instance : LawfulUpwardEnumerableLT UInt64 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .closed UInt64 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .closed UInt64 := inferInstance
instance : LawfulUpwardEnumerableLowerBound .open UInt64 := inferInstance
instance : LawfulUpwardEnumerableUpperBound .open UInt64 := inferInstance

instance : RangeSize .closed UInt64 where
  size bound a := bound.toNat + 1 - a.toNat

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed UInt64} {x : BitVec 64} :
    RangeSize.size bound (UInt64.ofBitVec x) = RangeSize.size (shape := .closed) bound.toBitVec x := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed UInt64 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt64.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 64) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    cases x
    simpa [rangeSizeSize_eq_toBitVec, UInt64.le_iff_toBitVec_le, succ?_ofBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec 64) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt64.le_iff_toBitVec_le, ← UInt64.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec 64) _ _ _

instance : RangeSize .open UInt64 := RangeSize.openOfClosed
instance : LawfulRangeSize .open UInt64 := inferInstance

end UInt64

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
