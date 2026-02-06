/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.ByteArray.Lemmas
import Init.Data.Nat.MinMax

/-!
# Basic lemmas about strings

This file contains lemmas that could be in `Init.Data.String.Basic` but are not because they are
not needed to define basic string operations.
-/

public section

namespace String

@[simp]
theorem singleton_append_inj : singleton c ++ s = singleton d ++ t ↔ c = d ∧ s = t := by
  simp [← toList_inj]

@[simp]
theorem push_inj : push s c = push t d ↔ s = t ∧ c = d := by
  simp [← toList_inj]

@[simp]
theorem append_eq_empty_iff {s t : String} : s ++ t = "" ↔ s = "" ∧ t = "" := by
  rw [← toList_inj]; simp

@[simp]
theorem append_eq_left_iff {s t : String} : s ++ t = s ↔ t = "" := by
  rw [← toList_inj]; simp

@[simp]
theorem append_eq_right_iff {s t : String} : s ++ t = t ↔ s = "" := by
  rw [← toList_inj]; simp

@[simp]
theorem empty_eq_iff : "" = s ↔ s = "" :=
  eq_comm

@[simp]
theorem push_ne_empty : push s c ≠ "" := by
  rw [ne_eq, ← toList_inj]; simp

@[simp]
theorem singleton_ne_empty {c : Char} : singleton c ≠ "" := by
  simp [singleton]

theorem empty_ne_singleton {c : Char} : "" ≠ singleton c := by
  simp

@[simp]
theorem Slice.Pos.copy_inj {s : Slice} {p₁ p₂ : s.Pos} : p₁.copy = p₂.copy ↔ p₁ = p₂ := by
  simp [String.Pos.ext_iff, Pos.ext_iff]

@[simp]
theorem Pos.startPos_le {s : String} (p : s.Pos) : s.startPos ≤ p := by
  simp [Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.startPos_le {s : Slice} (p : s.Pos) : s.startPos ≤ p := by
  simp [Pos.le_iff, Pos.Raw.le_iff]

theorem getUTF8Byte_eq_getUTF8Byte_toSlice {s : String} {p : String.Pos.Raw} {h} :
    s.getUTF8Byte p h = s.toSlice.getUTF8Byte p (by simpa) := by
  simp [Slice.getUTF8Byte]

theorem getUTF8Byte_toSlice {s : String} {p : String.Pos.Raw} {h} :
    s.toSlice.getUTF8Byte p h = s.getUTF8Byte p (by simpa) := by
  simp [Slice.getUTF8Byte]

@[simp]
theorem Pos.byte_toSlice {s : String} {p : s.Pos} {h} :
    p.toSlice.byte h = p.byte (ne_of_apply_ne Pos.toSlice (by simpa)) := by
  simp [byte]

theorem Pos.byte_eq_byte_toSlice {s : String} {p : s.Pos} {h} :
    p.byte h = p.toSlice.byte (ne_of_apply_ne Pos.ofToSlice (by simpa)) := by
  simp

theorem Slice.toByteArray_copy_slice {s : Slice} {p₁ p₂ : s.Pos} {h} :
    (s.slice p₁ p₂ h).copy.toByteArray = s.copy.toByteArray.extract p₁.offset.byteIdx p₂.offset.byteIdx := by
  simp [toByteArray_copy, ByteArray.extract_extract]
  rw [Nat.min_eq_left]
  simpa [String.Pos.le_iff, Pos.Raw.le_iff] using p₂.str_le_endExclusive

theorem toByteArray_copy_slice {s : String} {p₁ p₂ : s.Pos} {h} :
    (s.slice p₁ p₂ h).copy.toByteArray = s.toByteArray.extract p₁.offset.byteIdx p₂.offset.byteIdx := by
  simp [← slice_toSlice, Slice.toByteArray_copy_slice]

theorem Slice.utf8ByteSize_eq_size_toByteArray_copy {s : Slice} :
    s.utf8ByteSize = s.copy.toByteArray.size := by
  simp [utf8ByteSize_eq]

section Iterate

/-
These lemmas are slightly evil because they are non-definitional equalities between slices, but they
are useful and they are at least equalities between slices with definitionally equal underlying
strings, so it should be fine.
-/

@[simp]
theorem Slice.sliceTo_sliceFrom {s : Slice} {pos pos'} :
    (s.sliceFrom pos).sliceTo pos' =
      s.slice pos (Slice.Pos.ofSliceFrom pos') Slice.Pos.le_ofSliceFrom := by
  ext <;> simp [String.Pos.ext_iff, Pos.Raw.offsetBy_assoc]

@[simp]
theorem Slice.sliceFrom_sliceTo {s : Slice} {pos pos'} :
    (s.sliceTo pos).sliceFrom pos' =
      s.slice (Slice.Pos.ofSliceTo pos') pos Slice.Pos.ofSliceTo_le := by
  ext <;> simp [String.Pos.ext_iff]

@[simp]
theorem Slice.sliceFrom_sliceFrom {s : Slice} {pos pos'} :
    (s.sliceFrom pos).sliceFrom pos' =
      s.sliceFrom (Slice.Pos.ofSliceFrom pos') := by
  ext <;> simp [String.Pos.ext_iff, Pos.Raw.offsetBy_assoc]

@[simp]
theorem Slice.sliceTo_sliceTo {s : Slice} {pos pos'} :
    (s.sliceTo pos).sliceTo pos' = s.sliceTo (Slice.Pos.ofSliceTo pos') := by
  ext <;> simp [String.Pos.ext_iff]

end Iterate

theorem Slice.copy_eq_copy_slice {s : Slice} {pos₁ pos₂ : s.Pos} {h} :
    s.copy = (s.sliceTo pos₁).copy ++ (s.slice pos₁ pos₂ h).copy ++ (s.sliceFrom pos₂).copy := by
  simp [copy_eq_copy_sliceTo (pos := pos₂), copy_eq_copy_sliceTo (pos := Slice.Pos.sliceTo _ _ h)]

theorem copy_toByteArray_sliceTo {s : String} {pos : s.Pos} :
    (s.sliceTo pos).copy.toByteArray = s.toByteArray.extract 0 pos.offset.byteIdx := by
  simp [Slice.toByteArray_copy]

end String
