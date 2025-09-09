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

theorem succ?_eq_succ?_toBitVec {x : UInt8} :
    UpwardEnumerable.succ? x = UInt8.ofBitVec <$> UpwardEnumerable.succ? x.toBitVec := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← UInt8.toBitVec_inj]
  split <;> simp_all

theorem succMany?_eq_succMany?_toBitVec {k : Nat} {x : UInt8} :
    UpwardEnumerable.succMany? k x = UInt8.ofBitVec <$> UpwardEnumerable.succMany? k x.toBitVec := by
  simp [succMany?]

theorem ofBitVec_eq_iff {x : BitVec 8} {a : UInt8} :
    ofBitVec x = a ↔ x = a.toBitVec := by
  cases a; simp

theorem upwardEnumerableLE_iff_toBitVec {x y : UInt8} :
    UpwardEnumerable.LE x y ↔ UpwardEnumerable.LE x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LE, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

theorem upwardEnumerableLT_iff_toBitVec {x y : UInt8} :
    UpwardEnumerable.LT x y ↔ UpwardEnumerable.LT x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LT, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

instance : LawfulUpwardEnumerable UInt8 where
  ne_of_lt x y:= by
    simpa [upwardEnumerableLT_iff_toBitVec, ← UInt8.toBitVec_inj] using
      LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by simp [succMany?_eq_succMany?_toBitVec, succMany?_zero]
  succMany?_succ? a b := by
    simp [succMany?_eq_succMany?_toBitVec, succMany?_succ?, Option.bind_map,
      Function.comp_def, succ?_eq_succ?_toBitVec]

instance : LawfulUpwardEnumerableLE UInt8 where
  le_iff x y := by
    simpa [upwardEnumerableLE_iff_toBitVec, UInt8.le_iff_toBitVec_le] using
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

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed UInt8} {a : UInt8} :
    RangeSize.size bound a = RangeSize.size (shape := .closed) bound.toBitVec a.toBitVec := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed UInt8 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt8.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 8) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, succ?_eq_succ?_toBitVec] using
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

theorem succ?_eq_succ?_toBitVec {x : UInt16} :
    UpwardEnumerable.succ? x = UInt16.ofBitVec <$> UpwardEnumerable.succ? x.toBitVec := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← UInt16.toBitVec_inj]
  split <;> simp_all

theorem succMany?_eq_succMany?_toBitVec {k : Nat} {x : UInt16} :
    UpwardEnumerable.succMany? k x = UInt16.ofBitVec <$> UpwardEnumerable.succMany? k x.toBitVec := by
  simp [succMany?]

theorem ofBitVec_eq_iff {x : BitVec 16} {a : UInt16} :
    ofBitVec x = a ↔ x = a.toBitVec := by
  cases a; simp

theorem upwardEnumerableLE_iff_toBitVec {x y : UInt16} :
    UpwardEnumerable.LE x y ↔ UpwardEnumerable.LE x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LE, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

theorem upwardEnumerableLT_iff_toBitVec {x y : UInt16} :
    UpwardEnumerable.LT x y ↔ UpwardEnumerable.LT x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LT, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

instance : LawfulUpwardEnumerable UInt16 where
  ne_of_lt x y:= by
    simpa [upwardEnumerableLT_iff_toBitVec, ← UInt16.toBitVec_inj] using
      LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by simp [succMany?_eq_succMany?_toBitVec, succMany?_zero]
  succMany?_succ? a b := by
    simp [succMany?_eq_succMany?_toBitVec, succMany?_succ?, Option.bind_map,
      Function.comp_def, succ?_eq_succ?_toBitVec]

instance : LawfulUpwardEnumerableLE UInt16 where
  le_iff x y := by
    simpa [upwardEnumerableLE_iff_toBitVec, UInt16.le_iff_toBitVec_le] using
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

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed UInt16} {a : UInt16} :
    RangeSize.size bound a = RangeSize.size (shape := .closed) bound.toBitVec a.toBitVec := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed UInt16 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt16.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 16) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt16.le_iff_toBitVec_le, succ?_eq_succ?_toBitVec] using
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

theorem succ?_eq_succ?_toBitVec {x : UInt32} :
    UpwardEnumerable.succ? x = UInt32.ofBitVec <$> UpwardEnumerable.succ? x.toBitVec := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← UInt32.toBitVec_inj]
  split <;> simp_all

theorem succMany?_eq_succMany?_toBitVec {k : Nat} {x : UInt32} :
    UpwardEnumerable.succMany? k x = UInt32.ofBitVec <$> UpwardEnumerable.succMany? k x.toBitVec := by
  simp [succMany?]

theorem ofBitVec_eq_iff {x : BitVec 32} {a : UInt32} :
    ofBitVec x = a ↔ x = a.toBitVec := by
  cases a; simp

theorem upwardEnumerableLE_iff_toBitVec {x y : UInt32} :
    UpwardEnumerable.LE x y ↔ UpwardEnumerable.LE x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LE, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

theorem upwardEnumerableLT_iff_toBitVec {x y : UInt32} :
    UpwardEnumerable.LT x y ↔ UpwardEnumerable.LT x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LT, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

instance : LawfulUpwardEnumerable UInt32 where
  ne_of_lt x y:= by
    simpa [upwardEnumerableLT_iff_toBitVec, ← UInt32.toBitVec_inj] using
      LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by simp [succMany?_eq_succMany?_toBitVec, succMany?_zero]
  succMany?_succ? a b := by
    simp [succMany?_eq_succMany?_toBitVec, succMany?_succ?, Option.bind_map,
      Function.comp_def, succ?_eq_succ?_toBitVec]

instance : LawfulUpwardEnumerableLE UInt32 where
  le_iff x y := by
    simpa [upwardEnumerableLE_iff_toBitVec, UInt32.le_iff_toBitVec_le] using
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

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed UInt32} {a : UInt32} :
    RangeSize.size bound a = RangeSize.size (shape := .closed) bound.toBitVec a.toBitVec := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed UInt32 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt32.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 32) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt32.le_iff_toBitVec_le, succ?_eq_succ?_toBitVec] using
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

theorem succ?_eq_succ?_toBitVec {x : UInt64} :
    UpwardEnumerable.succ? x = UInt64.ofBitVec <$> UpwardEnumerable.succ? x.toBitVec := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← UInt64.toBitVec_inj]
  split <;> simp_all

theorem succMany?_eq_succMany?_toBitVec {k : Nat} {x : UInt64} :
    UpwardEnumerable.succMany? k x = UInt64.ofBitVec <$> UpwardEnumerable.succMany? k x.toBitVec := by
  simp [succMany?]

theorem ofBitVec_eq_iff {x : BitVec 64} {a : UInt64} :
    ofBitVec x = a ↔ x = a.toBitVec := by
  cases a; simp

theorem upwardEnumerableLE_iff_toBitVec {x y : UInt64} :
    UpwardEnumerable.LE x y ↔ UpwardEnumerable.LE x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LE, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

theorem upwardEnumerableLT_iff_toBitVec {x y : UInt64} :
    UpwardEnumerable.LT x y ↔ UpwardEnumerable.LT x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LT, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

instance : LawfulUpwardEnumerable UInt64 where
  ne_of_lt x y:= by
    simpa [upwardEnumerableLT_iff_toBitVec, ← UInt64.toBitVec_inj] using
      LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by simp [succMany?_eq_succMany?_toBitVec, succMany?_zero]
  succMany?_succ? a b := by
    simp [succMany?_eq_succMany?_toBitVec, succMany?_succ?, Option.bind_map,
      Function.comp_def, succ?_eq_succ?_toBitVec]

instance : LawfulUpwardEnumerableLE UInt64 where
  le_iff x y := by
    simpa [upwardEnumerableLE_iff_toBitVec, UInt64.le_iff_toBitVec_le] using
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

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed UInt64} {a : UInt64} :
    RangeSize.size bound a = RangeSize.size (shape := .closed) bound.toBitVec a.toBitVec := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed UInt64 where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt64.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec 64) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    simpa [rangeSizeSize_eq_toBitVec, UInt64.le_iff_toBitVec_le, succ?_eq_succ?_toBitVec] using
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

theorem succ?_eq_succ?_toBitVec {x : USize} :
    UpwardEnumerable.succ? x = USize.ofBitVec <$> UpwardEnumerable.succ? x.toBitVec := by
  simp only [succ?, BitVec.ofNat_eq_ofNat, Option.map_eq_map, ← USize.toBitVec_inj]
  split <;> simp_all

theorem succMany?_eq_succMany?_toBitVec {k : Nat} {x : USize} :
    UpwardEnumerable.succMany? k x = USize.ofBitVec <$> UpwardEnumerable.succMany? k x.toBitVec := by
  simp [succMany?]

theorem ofBitVec_eq_iff {x : BitVec System.Platform.numBits} {a : USize} :
    ofBitVec x = a ↔ x = a.toBitVec := by
  cases a; simp

theorem upwardEnumerableLE_iff_toBitVec {x y : USize} :
    UpwardEnumerable.LE x y ↔ UpwardEnumerable.LE x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LE, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

theorem upwardEnumerableLT_iff_toBitVec {x y : USize} :
    UpwardEnumerable.LT x y ↔ UpwardEnumerable.LT x.toBitVec y.toBitVec := by
  simp [UpwardEnumerable.LT, succMany?_eq_succMany?_toBitVec, ofBitVec_eq_iff]

instance : LawfulUpwardEnumerable USize where
  ne_of_lt x y:= by
    simpa [upwardEnumerableLT_iff_toBitVec, ← USize.toBitVec_inj] using
      LawfulUpwardEnumerable.ne_of_lt _ _
  succMany?_zero x := by simp [succMany?_eq_succMany?_toBitVec, succMany?_zero]
  succMany?_succ? a b := by
    simp [succMany?_eq_succMany?_toBitVec, succMany?_succ?, Option.bind_map,
      Function.comp_def, succ?_eq_succ?_toBitVec]

instance : LawfulUpwardEnumerableLE USize where
  le_iff x y := by
    simpa [upwardEnumerableLE_iff_toBitVec, USize.le_iff_toBitVec_le] using
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

theorem rangeSizeSize_eq_toBitVec {bound : Bound .closed USize} {a : USize} :
    RangeSize.size bound a = RangeSize.size (shape := .closed) bound.toBitVec a.toBitVec := by
  simp [RangeSize.size]

instance : LawfulRangeSize .closed USize where
  size_eq_zero_of_not_isSatisfied bound x := by
    simpa [rangeSizeSize_eq_toBitVec, USize.lt_iff_toBitVec_lt] using
      LawfulRangeSize.size_eq_zero_of_not_isSatisfied (su := .closed) (α := BitVec System.Platform.numBits) _ _
  size_eq_one_of_succ?_eq_none bound x := by
    simpa [rangeSizeSize_eq_toBitVec, USize.le_iff_toBitVec_le, succ?_eq_succ?_toBitVec] using
      LawfulRangeSize.size_eq_one_of_succ?_eq_none (su := .closed) (α := BitVec System.Platform.numBits) _ _
  size_eq_succ_of_succ?_eq_some bound init x := by
    simpa [rangeSizeSize_eq_toBitVec, USize.le_iff_toBitVec_le, ← USize.toBitVec_inj, succ?] using
      LawfulRangeSize.size_eq_succ_of_succ?_eq_some (su := .closed) (α := BitVec System.Platform.numBits) _ _ _

instance : RangeSize .open USize := RangeSize.openOfClosed
instance : LawfulRangeSize .open USize := inferInstance

end USize
