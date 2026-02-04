/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Basic

public section

namespace String

@[simp]
theorem Slice.Pos.next_le_iff_lt {s : Slice} {p q : s.Pos} {h} : p.next h ≤ q ↔ p < q :=
  ⟨fun h => Std.lt_of_lt_of_le lt_next h, next_le_of_lt⟩

@[simp]
theorem Slice.Pos.lt_next_iff_le {s : Slice} {p q : s.Pos} {h} : p < q.next h ↔ p ≤ q := by
  rw [← Decidable.not_iff_not, Std.not_lt, next_le_iff_lt, Std.not_le]

@[simp]
theorem Pos.next_le_iff_lt {s : String} {p q : s.Pos} {h} : p.next h ≤ q ↔ p < q := by
  rw [next, Pos.ofToSlice_le_iff, ← Pos.toSlice_lt_toSlice_iff]
  exact Slice.Pos.next_le_iff_lt

@[simp]
theorem Slice.Pos.le_startPos {s : Slice} (p : s.Pos) : p ≤ s.startPos ↔ p = s.startPos :=
  ⟨fun h => Std.le_antisymm h (startPos_le _), by simp +contextual⟩

@[simp]
theorem Slice.Pos.startPos_lt_iff {s : Slice} (p : s.Pos) : s.startPos < p ↔ p ≠ s.startPos := by
  simp [← le_startPos, Std.not_le]

@[simp]
theorem Slice.Pos.endPos_le {s : Slice} (p : s.Pos) : s.endPos ≤ p ↔ p = s.endPos :=
  ⟨fun h => Std.le_antisymm (le_endPos _) h, by simp +contextual⟩

@[simp]
theorem Pos.le_startPos {s : String} (p : s.Pos) : p ≤ s.startPos ↔ p = s.startPos :=
  ⟨fun h => Std.le_antisymm h (startPos_le _), by simp +contextual⟩

@[simp]
theorem Pos.endPos_le {s : String} (p : s.Pos) : s.endPos ≤ p ↔ p = s.endPos :=
  ⟨fun h => Std.le_antisymm (le_endPos _) h, by simp +contextual [Std.le_refl]⟩

@[simp]
theorem Slice.Pos.not_lt_startPos {s : Slice} {p : s.Pos} : ¬ p < s.startPos :=
  fun h => Std.lt_irrefl (Std.lt_of_lt_of_le h (Slice.Pos.startPos_le _))

theorem Slice.Pos.ne_startPos_of_lt {s : Slice} {p q : s.Pos} : p < q → q ≠ s.startPos := by
  rintro h rfl
  simp at h

@[simp]
theorem Slice.Pos.next_ne_startPos {s : Slice} {p : s.Pos} {h} :
    p.next h ≠ s.startPos :=
  ne_startPos_of_lt lt_next

theorem Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceFrom p).Pos} : Slice.Pos.ofSliceFrom q < Slice.Pos.ofSliceFrom r ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff]

theorem Slice.Pos.ofSliceFrom_le_ofSliceFrom_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceFrom p).Pos} : Slice.Pos.ofSliceFrom q ≤ Slice.Pos.ofSliceFrom r ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.offset_le_rawEndPos {s : Slice} {p : s.Pos} :
    p.offset ≤ s.rawEndPos :=
  p.isValidForSlice.le_rawEndPos

@[simp]
theorem Pos.offset_le_rawEndPos {s : String} {p : s.Pos} :
    p.offset ≤ s.rawEndPos :=
  p.isValid.le_rawEndPos

@[simp]
theorem Slice.Pos.offset_lt_rawEndPos_iff {s : Slice} {p : s.Pos} :
    p.offset < s.rawEndPos ↔ p ≠ s.endPos := by
  simp [Std.lt_iff_le_and_ne, p.offset_le_rawEndPos, Pos.ext_iff]

@[simp]
theorem Pos.offset_lt_rawEndPos_iff {s : String} {p : s.Pos} :
    p.offset < s.rawEndPos ↔ p ≠ s.endPos := by
  simp [Std.lt_iff_le_and_ne, p.offset_le_rawEndPos, Pos.ext_iff]

@[simp]
theorem Slice.Pos.getUTF8Byte_offset {s : Slice} {p : s.Pos} {h} :
    s.getUTF8Byte p.offset h = p.byte (by simpa using h) := by
  simp [Pos.byte]

theorem Slice.Pos.isUTF8FirstByte_getUTF8Byte_offset {s : Slice} {p : s.Pos} {h} :
    (s.getUTF8Byte p.offset h).IsUTF8FirstByte := by
  simpa [getUTF8Byte_offset] using isUTF8FirstByte_byte

theorem Pos.getUTF8Byte_offset {s : String} {p : s.Pos} {h} :
    s.getUTF8Byte p.offset h = p.byte (by simpa using h) := by
  simp only [getUTF8Byte_eq_getUTF8Byte_toSlice, ← Pos.offset_toSlice,
    Slice.Pos.getUTF8Byte_offset, byte_toSlice]

theorem Pos.isUTF8FirstByte_getUTF8Byte_offset {s : String} {p : s.Pos} {h} :
    (s.getUTF8Byte p.offset h).IsUTF8FirstByte := by
  simpa [getUTF8Byte_offset] using isUTF8FirstByte_byte

end String
