/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Julia Markus Himmel
-/
module

prelude
public import Init.Data.String.TakeDrop
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop
import Init.Data.String.Lemmas.Splits

public section

namespace String

namespace Slice

theorem drop_eq_sliceFrom {s : Slice} {n : Nat} : s.drop n = s.sliceFrom (s.startPos.nextn n) :=
  (rfl)

@[simp]
theorem toList_copy_drop {s : Slice} {n : Nat} : (s.drop n).copy.toList = s.copy.toList.drop n := by
  simp [drop_eq_sliceFrom, (s.splits_nextn_startPos n).copy_sliceFrom_eq]

theorem dropEnd_eq_sliceTo {s : Slice} {n : Nat} : s.dropEnd n = s.sliceTo (s.endPos.prevn n) :=
  (rfl)

@[simp]
theorem toList_copy_dropEnd {s : Slice} {n : Nat} :
    (s.dropEnd n).copy.toList = s.copy.toList.take (s.copy.length - n) := by
  simp [dropEnd_eq_sliceTo, (s.splits_prevn_endPos n).copy_sliceTo_eq]

theorem take_eq_sliceTo {s : Slice} {n : Nat} : s.take n = s.sliceTo (s.startPos.nextn n) :=
  (rfl)

@[simp]
theorem toList_copy_take {s : Slice} {n : Nat} : (s.take n).copy.toList = s.copy.toList.take n := by
  simp [take_eq_sliceTo, (s.splits_nextn_startPos n).copy_sliceTo_eq]

theorem takeEnd_eq_sliceFrom {s : Slice} {n : Nat} : s.takeEnd n = s.sliceFrom (s.endPos.prevn n) :=
  (rfl)

@[simp]
theorem toList_copy_takeEnd {s : Slice} {n : Nat} :
    (s.takeEnd n).copy.toList = s.copy.toList.drop (s.copy.length - n) := by
  simp [takeEnd_eq_sliceFrom, (s.splits_prevn_endPos n).copy_sliceFrom_eq]

end Slice

@[simp]
theorem drop_toSlice {s : String} {n : Nat} : s.toSlice.drop n = s.drop n :=
  (rfl)

@[simp]
theorem toList_copy_drop {s : String} {n : Nat} : (s.drop n).copy.toList = s.toList.drop n := by
  simp [← drop_toSlice]

@[simp]
theorem dropEnd_toSlice {s : String} {n : Nat} : s.toSlice.dropEnd n = s.dropEnd n :=
  (rfl)

@[simp]
theorem toList_copy_dropEnd {s : String} {n : Nat} :
    (s.dropEnd n).copy.toList = s.toList.take (s.length - n) := by
  simp [← dropEnd_toSlice]

@[simp]
theorem take_toSlice {s : String} {n : Nat} : s.toSlice.take n = s.take n :=
  (rfl)

@[simp]
theorem toList_copy_take {s : String} {n : Nat} : (s.take n).copy.toList = s.toList.take n := by
  simp [← take_toSlice]

@[simp]
theorem takeEnd_toSlice {s : String} {n : Nat} : s.toSlice.takeEnd n = s.takeEnd n :=
  (rfl)

@[simp]
theorem toList_copy_takeEnd {s : String} {n : Nat} :
    (s.takeEnd n).copy.toList = s.toList.drop (s.length - n) := by
  simp [← takeEnd_toSlice]

end String
