/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import all Init.Data.String.Basic
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
theorem singleton_inj {c d : Char} : singleton c = singleton d ↔ c = d := by
  simp [← toList_inj]

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
theorem ofList_cons {c : Char} {l : List Char} :
    String.ofList (c :: l) = String.singleton c ++ String.ofList l := by
  simp [← toList_inj]

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
    p.toSlice.byte h = p.byte (ne_of_apply_ne Pos.toSlice (by simpa using h)) := by
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

@[ext (iff := false)]
theorem Slice.ext {s t : Slice} (h : s.str = t.str)
    (hsi : s.startInclusive.cast h = t.startInclusive)
    (hee : s.endExclusive.cast h = t.endExclusive) : s = t := by
  rcases s with ⟨s, s₁, e₁, h₁⟩
  rcases t with ⟨t, s₂, e₂, h₂⟩
  cases h
  simp_all

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
  ext <;> simp [Pos.Raw.offsetBy_assoc]

@[simp]
theorem Slice.sliceFrom_sliceTo {s : Slice} {pos pos'} :
    (s.sliceTo pos).sliceFrom pos' =
      s.slice (Slice.Pos.ofSliceTo pos') pos Slice.Pos.ofSliceTo_le := by
  ext <;> simp

@[simp]
theorem Slice.sliceFrom_sliceFrom {s : Slice} {pos pos'} :
    (s.sliceFrom pos).sliceFrom pos' =
      s.sliceFrom (Slice.Pos.ofSliceFrom pos') := by
  ext <;> simp [Pos.Raw.offsetBy_assoc]

@[simp]
theorem Slice.sliceTo_sliceTo {s : Slice} {pos pos'} :
    (s.sliceTo pos).sliceTo pos' = s.sliceTo (Slice.Pos.ofSliceTo pos') := by
  ext <;> simp

@[simp]
theorem Slice.sliceFrom_slice {s : Slice} {p₁ p₂ h p} :
    (s.slice p₁ p₂ h).sliceFrom p = s.slice (Pos.ofSlice p) p₂ Pos.ofSlice_le := by
  ext <;> simp [Nat.add_assoc]

@[simp]
theorem Slice.sliceTo_slice {s : Slice} {p₁ p₂ h p} :
    (s.slice p₁ p₂ h).sliceTo p = s.slice p₁ (Pos.ofSlice p) Pos.le_ofSlice := by
  ext <;> simp [Nat.add_assoc]

@[simp]
theorem sliceTo_sliceFrom {s : String} {pos pos'} :
    (s.sliceFrom pos).sliceTo pos' =
      s.slice pos (Pos.ofSliceFrom pos') Pos.le_ofSliceFrom := by
  ext <;> simp

@[simp]
theorem sliceFrom_sliceTo {s : String} {pos pos'} :
    (s.sliceTo pos).sliceFrom pos' =
      s.slice (Pos.ofSliceTo pos') pos Pos.ofSliceTo_le := by
  ext <;> simp

@[simp]
theorem sliceFrom_sliceFrom {s : String} {pos pos'} :
    (s.sliceFrom pos).sliceFrom pos' =
      s.sliceFrom (Pos.ofSliceFrom pos') := by
  ext <;> simp

@[simp]
theorem sliceTo_sliceTo {s : String} {pos pos'} :
    (s.sliceTo pos).sliceTo pos' = s.sliceTo (Pos.ofSliceTo pos') := by
  ext <;> simp

@[simp]
theorem sliceFrom_slice {s : String} {p₁ p₂ h p} :
    (s.slice p₁ p₂ h).sliceFrom p = s.slice (Pos.ofSlice p) p₂ Pos.ofSlice_le := by
  ext <;> simp

@[simp]
theorem sliceTo_slice {s : String} {p₁ p₂ h p} :
    (s.slice p₁ p₂ h).sliceTo p = s.slice p₁ (Pos.ofSlice p) Pos.le_ofSlice := by
  ext <;> simp

@[simp]
theorem Slice.sliceFrom_startPos {s : Slice} : s.sliceFrom s.startPos = s := by
  ext <;> simp

@[simp]
theorem Slice.sliceFrom_eq_self_iff {s : Slice} {p : s.Pos} : s.sliceFrom p = s ↔ p = s.startPos := by
  refine ⟨?_, by rintro rfl; simp⟩
  rcases s with ⟨str, startInclusive, endExclusive, h⟩
  simp [sliceFrom, Slice.startPos, String.Pos.ext_iff, Pos.Raw.ext_iff, Slice.Pos.ext_iff]

@[simp]
theorem Slice.sliceTo_endPos {s : Slice} : s.sliceTo s.endPos = s := by
  ext <;> simp

@[simp]
theorem Slice.sliceTo_eq_self_iff {s : Slice} {p : s.Pos} : s.sliceTo p = s ↔ p = s.endPos := by
  refine ⟨?_, by rintro rfl; simp⟩
  rcases s with ⟨str, startInclusive, endExclusive, h⟩
  simp [sliceTo, Slice.endPos, String.Pos.ext_iff, Pos.Raw.ext_iff, Slice.Pos.ext_iff,
    utf8ByteSize_eq]
  omega

@[simp]
theorem Slice.slice_startPos {s : Slice} {p : s.Pos} :
    s.slice s.startPos p (Pos.startPos_le _) = s.sliceTo p := by
  ext <;> simp

@[simp]
theorem Slice.slice_eq_self_iff {s : Slice} {p₁ p₂ : s.Pos} {h} :
    s.slice p₁ p₂ h = s ↔ p₁ = s.startPos ∧ p₂ = s.endPos := by
  refine ⟨?_, by rintro ⟨rfl, rfl⟩; simp⟩
  rcases s with ⟨str, startInclusive, endExclusive, h⟩
  simp [slice, Slice.endPos, String.Pos.ext_iff, Pos.Raw.ext_iff, Slice.Pos.ext_iff,
    utf8ByteSize_eq]
  omega

@[simp]
theorem Slice.slice_endPos {s : Slice} {p : s.Pos} :
    s.slice p s.endPos (Pos.le_endPos _) = s.sliceFrom p := by
  ext <;> simp

@[simp]
theorem sliceFrom_startPos {s : String} : s.sliceFrom s.startPos = s := by
  ext <;> simp

@[simp]
theorem sliceFrom_eq_toSlice_iff {s : String} {p : s.Pos} : s.sliceFrom p = s.toSlice ↔ p = s.startPos := by
  simp [← sliceFrom_toSlice]

@[simp]
theorem sliceTo_endPos {s : String} : s.sliceTo s.endPos = s := by
  ext <;> simp

@[simp]
theorem sliceTo_eq_toSlice_iff {s : String} {p : s.Pos} : s.sliceTo p = s.toSlice ↔ p = s.endPos := by
  simp [← sliceTo_toSlice]

@[simp]
theorem slice_startPos {s : String} {p : s.Pos} :
    s.slice s.startPos p (Pos.startPos_le _) = s.sliceTo p := by
  ext <;> simp

@[simp]
theorem slice_endPos {s : String} {p : s.Pos} :
    s.slice p s.endPos (Pos.le_endPos _) = s.sliceFrom p := by
  ext <;> simp

@[simp]
theorem slice_eq_toSlice_iff {s : String} {p₁ p₂ : s.Pos} {h} :
    s.slice p₁ p₂ h = s.toSlice ↔ p₁ = s.startPos ∧ p₂ = s.endPos := by
  simp [← slice_toSlice]

end Iterate

theorem Slice.copy_eq_copy_slice {s : Slice} {pos₁ pos₂ : s.Pos} {h} :
    s.copy = (s.sliceTo pos₁).copy ++ (s.slice pos₁ pos₂ h).copy ++ (s.sliceFrom pos₂).copy := by
  simp [copy_eq_copy_sliceTo (pos := pos₂), copy_eq_copy_sliceTo (pos := Slice.Pos.sliceTo _ _ h)]

theorem copy_toByteArray_sliceTo {s : String} {pos : s.Pos} :
    (s.sliceTo pos).copy.toByteArray = s.toByteArray.extract 0 pos.offset.byteIdx := by
  simp [Slice.toByteArray_copy]

theorem Slice.pos!_eq_pos {s : Slice} {p : Pos.Raw} (h : p.IsValidForSlice s) :
    s.pos! p = s.pos p h := by
  simp [Slice.pos!, h]

theorem pos!_eq_pos {s : String} {p : Pos.Raw} (h : p.IsValid s) :
    s.pos! p = s.pos p h := by
  rw [String.pos!, Slice.pos!_eq_pos h.toSlice, String.pos]

@[simp]
theorem Slice.copy_pos {s : Slice} {p : Pos.Raw} {h : Pos.Raw.IsValidForSlice s p} :
    (s.pos p h).copy = s.copy.pos p (Pos.Raw.isValid_copy_iff.2 h) := by
  simp [String.Pos.ext_iff]

@[simp]
theorem Slice.cast_pos {s t : Slice} {p : Pos.Raw} {h : Pos.Raw.IsValidForSlice s p}
    {h' : s.copy = t.copy} {h'' : Pos.Raw.IsValidForSlice t p} :
    (s.pos p h).cast h' = t.pos p h'' := by
  simp [Slice.Pos.ext_iff]

@[simp]
theorem cast_pos {s t : String} {p : Pos.Raw} {h : Pos.Raw.IsValid s p} {h' : s = t} :
    (s.pos p h).cast h' = t.pos p (h' ▸ h) := by
  simp [String.Pos.ext_iff]

@[simp]
theorem Pos.Raw.isValidForSlice_zero {s : Slice} : (0 : Pos.Raw).IsValidForSlice s where
  le_rawEndPos := by simp [Pos.Raw.le_iff]
  isValid_offsetBy := by simpa using s.startInclusive.isValid

@[simp]
theorem Pos.get_ofToSlice {s : String} {p : (s.toSlice).Pos} {h} :
    (ofToSlice p).get h = p.get (by simpa [← ofToSlice_inj]) := by
  simp [get_eq_get_toSlice]

@[simp]
theorem push_empty {c : Char} : "".push c = singleton c := rfl

namespace Slice.Pos

@[simp]
theorem nextn_zero {s : Slice} {p : s.Pos} : p.nextn 0 = p := by
  simp [nextn]

theorem nextn_add_one {s : Slice} {p : s.Pos} :
    p.nextn (n + 1) = if h : p = s.endPos then p else (p.next h).nextn n := by
  simp [nextn]

@[simp]
theorem nextn_endPos {s : Slice} : s.endPos.nextn n = s.endPos := by
  cases n <;> simp [nextn_add_one]

end Slice.Pos

namespace Pos

theorem nextn_eq_nextn_toSlice {s : String} {p : s.Pos} : p.nextn n = Pos.ofToSlice (p.toSlice.nextn n) :=
  (rfl)

@[simp]
theorem nextn_zero {s : String} {p : s.Pos} : p.nextn 0 = p := by
  simp [nextn_eq_nextn_toSlice]

theorem nextn_add_one {s : String} {p : s.Pos} :
    p.nextn (n + 1) = if h : p = s.endPos then p else (p.next h).nextn n := by
  simp only [nextn_eq_nextn_toSlice, Slice.Pos.nextn_add_one, endPos_toSlice, toSlice_inj]
  split <;> simp [Pos.next_toSlice]

theorem nextn_toSlice {s : String} {p : s.Pos} : p.toSlice.nextn n = (p.nextn n).toSlice := by
  induction n generalizing p with simp_all [nextn_add_one, Slice.Pos.nextn_add_one, apply_dite Pos.toSlice, next_toSlice]

theorem toSlice_nextn {s : String} {p : s.Pos} : (p.nextn n).toSlice = p.toSlice.nextn n :=
  nextn_toSlice.symm

@[simp]
theorem nextn_endPos {s : String} : s.endPos.nextn n = s.endPos := by
  cases n <;> simp [nextn_add_one]

end Pos

@[simp]
theorem Slice.Pos.cast_toSlice_copy {s : Slice} {pos : s.Pos} :
    pos.copy.toSlice.cast (by simp) = pos := by
  ext; simp

@[simp]
theorem Slice.Pos.sliceFrom_eq_startPos {s : Slice} {p : s.Pos} :
    (Pos.sliceFrom p p (Pos.le_refl _)) = Slice.startPos _ := by
  simp [← Pos.ofSliceFrom_inj]

@[simp]
theorem Slice.Pos.sliceFrom_endPos {s : Slice} {p : s.Pos} :
    (Pos.sliceFrom p s.endPos (Pos.le_endPos _)) = Slice.endPos _ := by
  simp [← Pos.ofSliceFrom_inj]

@[simp]
theorem Slice.Pos.sliceTo_startPos {s : Slice} {p : s.Pos} :
    (Pos.sliceTo p s.startPos (Pos.startPos_le _)) = Slice.startPos _ := by
  simp [← Pos.ofSliceTo_inj]

@[simp]
theorem Slice.Pos.sliceTo_eq_endPos {s : Slice} {p : s.Pos} :
    (Pos.sliceTo p p (Pos.le_refl _)) = Slice.endPos _ := by
  simp [← Pos.ofSliceTo_inj]

@[simp]
theorem Slice.Pos.slice_eq_startPos {s : Slice} {p₀ p₁ : s.Pos} {h} :
    (Pos.slice p₀ p₀ p₁ (Pos.le_refl _) h) = Slice.startPos _ := by
  simp [← Pos.ofSlice_inj]

@[simp]
theorem Slice.Pos.slice_eq_endPos {s : Slice} {p₀ p₁ : s.Pos} {h} :
    (Pos.slice p₁ p₀ p₁ h (Pos.le_refl _)) = Slice.endPos _ := by
  simp [← Pos.ofSlice_inj]

end String
