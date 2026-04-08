/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Range.Polymorphic.BitVec
public import Init.Data.UInt
import Init.ByCases
import Init.Data.BitVec.Lemmas
import Init.Data.Option.Lemmas

public section

open Std Std.PRange

namespace UInt8

instance : UpwardEnumerable UInt8 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt8.size then some (.ofNatLT _ h) else none

instance : Least? UInt8 where
  least? := some 0

instance : LawfulUpwardEnumerableLeast? UInt8 where
  least?_le a := ⟨0, rfl, a.toNat, by simpa [succMany?] using UInt8.toNat_lt a⟩

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
  succMany?_add_one n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE UInt8 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, UInt8.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulUpwardEnumerableLT UInt8 := inferInstance

instance : Rxc.HasSize UInt8 where
  size lo hi := hi.toNat + 1 - lo.toNat

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (UInt8.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  simp [Rxc.HasSize.size]

instance : Rxc.LawfulHasSize UInt8 where
  size_eq_zero_of_not_le lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, UInt8.lt_iff_toBitVec_lt] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec 8) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, succ?_ofBitVec] using
      Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 8) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    cases lo; cases x
    simpa [rxcHasSize_eq_toBitVec, UInt8.le_iff_toBitVec_le, ← UInt8.toBitVec_inj, succ?] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 8) _ _ _

instance : Rxc.IsAlwaysFinite UInt8 := inferInstance

instance : Rxo.HasSize UInt8 := .ofClosed
instance : Rxo.LawfulHasSize UInt8 := inferInstance
instance : Rxo.IsAlwaysFinite UInt8 := inferInstance

instance : Rxi.HasSize UInt8 where
  size lo := 2 ^ 8 - lo.toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (UInt8.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size]

instance : Rxi.LawfulHasSize UInt8 where
  size_eq_one_of_succ?_eq_none lo := by
    cases lo
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 8) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    cases lo; cases lo'
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 8) _ _

end UInt8

namespace UInt16

instance : UpwardEnumerable UInt16 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt16.size then some (.ofNatLT _ h) else none

instance : Least? UInt16 where
  least? := some 0

instance : LawfulUpwardEnumerableLeast? UInt16 where
  least?_le a := ⟨0, rfl, a.toNat, by simpa [succMany?] using UInt16.toNat_lt a⟩

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
  succMany?_add_one n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE UInt16 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, UInt16.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulUpwardEnumerableLT UInt16 := inferInstance

instance : Rxc.HasSize UInt16 where
  size lo hi := hi.toNat + 1 - lo.toNat

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (UInt16.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  simp [Rxc.HasSize.size]

instance : Rxc.LawfulHasSize UInt16 where
  size_eq_zero_of_not_le lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, UInt16.lt_iff_toBitVec_lt] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec 16) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, UInt16.le_iff_toBitVec_le, succ?_ofBitVec] using
      Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 16) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    cases lo; cases x
    simpa [rxcHasSize_eq_toBitVec, UInt16.le_iff_toBitVec_le, ← UInt16.toBitVec_inj, succ?] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 16) _ _ _

instance : Rxc.IsAlwaysFinite UInt16 := inferInstance

instance : Rxo.HasSize UInt16 := .ofClosed
instance : Rxo.LawfulHasSize UInt16 := inferInstance
instance : Rxo.IsAlwaysFinite UInt16 := inferInstance

instance : Rxi.HasSize UInt16 where
  size lo := 2 ^ 16 - lo.toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (UInt16.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size]

instance : Rxi.LawfulHasSize UInt16 where
  size_eq_one_of_succ?_eq_none lo := by
    cases lo
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 16) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    cases lo; cases lo'
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 16) _ _

end UInt16

namespace UInt32

instance : UpwardEnumerable UInt32 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt32.size then some (.ofNatLT _ h) else none

instance : Least? UInt32 where
  least? := some 0

instance : LawfulUpwardEnumerableLeast? UInt32 where
  least?_le a := ⟨0, rfl, a.toNat, by simpa [succMany?] using UInt32.toNat_lt a⟩

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
  succMany?_add_one n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE UInt32 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, UInt32.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulUpwardEnumerableLT UInt32 := inferInstance

instance : Rxc.HasSize UInt32 where
  size lo hi := hi.toNat + 1 - lo.toNat

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (UInt32.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  simp [Rxc.HasSize.size]

instance : Rxc.LawfulHasSize UInt32 where
  size_eq_zero_of_not_le lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, UInt32.lt_iff_toBitVec_lt] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec 32) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, UInt32.le_iff_toBitVec_le, succ?_ofBitVec] using
      Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 32) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    cases lo; cases x
    simpa [rxcHasSize_eq_toBitVec, UInt32.le_iff_toBitVec_le, ← UInt32.toBitVec_inj, succ?] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 32) _ _ _

instance : Rxc.IsAlwaysFinite UInt32 := inferInstance

instance : Rxo.HasSize UInt32 := .ofClosed
instance : Rxo.LawfulHasSize UInt32 := inferInstance
instance : Rxo.IsAlwaysFinite UInt32 := inferInstance

instance : Rxi.HasSize UInt32 where
  size lo := 2 ^ 32 - lo.toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (UInt32.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size]

instance : Rxi.LawfulHasSize UInt32 where
  size_eq_one_of_succ?_eq_none lo := by
    cases lo
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 32) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    cases lo; cases lo'
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 32) _ _

end UInt32

namespace UInt64

instance : UpwardEnumerable UInt64 where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < UInt64.size then some (.ofNatLT _ h) else none

instance : Least? UInt64 where
  least? := some 0

instance : LawfulUpwardEnumerableLeast? UInt64 where
  least?_le a := ⟨0, rfl, a.toNat, by simpa [succMany?] using UInt64.toNat_lt a⟩

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
  succMany?_add_one n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE UInt64 where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, UInt64.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulUpwardEnumerableLT UInt64 := inferInstance

instance : Rxc.HasSize UInt64 where
  size lo hi := hi.toNat + 1 - lo.toNat

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (UInt64.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  simp [Rxc.HasSize.size]

instance : Rxc.LawfulHasSize UInt64 where
  size_eq_zero_of_not_le lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, UInt64.lt_iff_toBitVec_lt] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec 64) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, UInt64.le_iff_toBitVec_le, succ?_ofBitVec] using
      Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 64) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    cases lo; cases x
    simpa [rxcHasSize_eq_toBitVec, UInt64.le_iff_toBitVec_le, ← UInt64.toBitVec_inj, succ?] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 64) _ _ _

instance : Rxc.IsAlwaysFinite UInt64 := inferInstance

instance : Rxo.HasSize UInt64 := .ofClosed
instance : Rxo.LawfulHasSize UInt64 := inferInstance
instance : Rxo.IsAlwaysFinite UInt64 := inferInstance

instance : Rxi.HasSize UInt64 where
  size lo := 2 ^ 64 - lo.toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (UInt64.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size]

instance : Rxi.LawfulHasSize UInt64 where
  size_eq_one_of_succ?_eq_none lo := by
    cases lo
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec 64) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    cases lo; cases lo'
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec 64) _ _

end UInt64

namespace USize

instance : UpwardEnumerable USize where
  succ? i := if i + 1 = 0 then none else some (i + 1)
  succMany? n i := if h : i.toNat + n < USize.size then some (.ofNatLT _ h) else none

instance : Least? USize where
  least? := some 0

instance : LawfulUpwardEnumerableLeast? USize where
  least?_le a := ⟨0, rfl, a.toNat, by simpa [succMany?] using USize.toNat_lt_size a⟩

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
  succMany?_add_one n x := by
    cases x
    simp [succMany?_ofBitVec, succMany?_add_one, Option.bind_map, Function.comp_def,
      succ?_ofBitVec]

instance : LawfulUpwardEnumerableLE USize where
  le_iff x y := by
    cases x; cases y
    simpa [upwardEnumerableLE_ofBitVec, USize.le_iff_toBitVec_le] using
      LawfulUpwardEnumerableLE.le_iff _ _

instance : LawfulUpwardEnumerableLT USize := inferInstance

instance : Rxc.HasSize USize where
  size lo hi := hi.toNat + 1 - lo.toNat

theorem rxcHasSize_eq_toBitVec :
    Rxc.HasSize.size (USize.ofBitVec lo) hi = Rxc.HasSize.size lo hi.toBitVec := by
  simp [Rxc.HasSize.size]

instance : Rxc.LawfulHasSize USize where
  size_eq_zero_of_not_le lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, USize.lt_iff_toBitVec_lt] using
      Rxc.LawfulHasSize.size_eq_zero_of_not_le (α := BitVec System.Platform.numBits) _ _
  size_eq_one_of_succ?_eq_none lo hi := by
    cases lo
    simpa [rxcHasSize_eq_toBitVec, USize.le_iff_toBitVec_le, succ?_ofBitVec] using
      Rxc.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec System.Platform.numBits) _ _
  size_eq_succ_of_succ?_eq_some lo hi x := by
    cases lo; cases x
    simpa [rxcHasSize_eq_toBitVec, USize.le_iff_toBitVec_le, ← USize.toBitVec_inj, succ?] using
      Rxc.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec System.Platform.numBits) _ _ _

instance : Rxc.IsAlwaysFinite USize := inferInstance

instance : Rxo.HasSize USize := .ofClosed
instance : Rxo.LawfulHasSize USize := inferInstance
instance : Rxo.IsAlwaysFinite USize := inferInstance

instance : Rxi.HasSize USize where
  size lo := 2 ^ System.Platform.numBits - lo.toNat

theorem rxiHasSize_eq_toBitVec :
    Rxi.HasSize.size (USize.ofBitVec lo) = Rxi.HasSize.size lo := by
  simp [Rxi.HasSize.size]

instance : Rxi.LawfulHasSize USize where
  size_eq_one_of_succ?_eq_none lo := by
    cases lo
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_one_of_succ?_eq_none (α := BitVec System.Platform.numBits) _
  size_eq_succ_of_succ?_eq_some lo lo' := by
    cases lo; cases lo'
    simpa [rxiHasSize_eq_toBitVec, succ?_ofBitVec] using
      Rxi.LawfulHasSize.size_eq_succ_of_succ?_eq_some (α := BitVec System.Platform.numBits) _ _

end USize
