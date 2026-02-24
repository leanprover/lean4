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
import Init.Data.Order.Lemmas
import Init.Omega

public section

namespace String

@[simp]
theorem Slice.Pos.next_le_iff_lt {s : Slice} {p q : s.Pos} {h} : p.next h ≤ q ↔ p < q :=
  ⟨fun h => Std.lt_of_lt_of_le lt_next h, next_le_of_lt⟩

@[simp]
theorem Slice.Pos.lt_next_iff_le {s : Slice} {p q : s.Pos} {h} : p < q.next h ↔ p ≤ q := by
  rw [← Decidable.not_iff_not, Std.not_lt, next_le_iff_lt, Std.not_le]

theorem Slice.Pos.next_eq_iff {s : Slice} {p q : s.Pos} {h} :
    p.next h = q ↔ p < q ∧ ∀ (q' : s.Pos), p < q' → q ≤ q' :=
  ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => Std.le_antisymm (by simpa) (h₂ _ (by simp))⟩

@[simp]
theorem Pos.next_le_iff_lt {s : String} {p q : s.Pos} {h} : p.next h ≤ q ↔ p < q := by
  rw [next, Pos.ofToSlice_le_iff, ← Pos.toSlice_lt_toSlice_iff]
  exact Slice.Pos.next_le_iff_lt

@[simp]
theorem Pos.lt_next_iff_le {s : String} {p q : s.Pos} {h} : p < q.next h ↔ p ≤ q := by
  rw [← Std.not_le, next_le_iff_lt, Std.not_lt]

theorem Pos.next_eq_iff {s : String} {p q : s.Pos} {h} :
    p.next h = q ↔ p < q ∧ ∀ (q' : s.Pos), p < q' → q ≤ q' :=
  ⟨by rintro rfl; simp, fun ⟨h₁, h₂⟩ => Std.le_antisymm (by simpa) (h₂ _ (by simp))⟩

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
theorem Slice.Pos.lt_endPos_iff {s : Slice} (p : s.Pos) : p < s.endPos ↔ p ≠ s.endPos := by
  simp [← endPos_le, Std.not_le]

@[simp]
theorem Pos.le_startPos {s : String} (p : s.Pos) : p ≤ s.startPos ↔ p = s.startPos :=
  ⟨fun h => Std.le_antisymm h (startPos_le _), by simp +contextual⟩

@[simp]
theorem Pos.startPos_lt_iff {s : String} {p : s.Pos} : s.startPos < p ↔ p ≠ s.startPos := by
  simp [← le_startPos, Std.not_le]

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
theorem Pos.not_lt_startPos {s : String} {p : s.Pos} : ¬ p < s.startPos :=
  fun h => Std.lt_irrefl (Std.lt_of_lt_of_le h (Pos.startPos_le _))

@[simp]
theorem Slice.Pos.not_endPos_lt {s : Slice} {p : s.Pos} : ¬ s.endPos < p :=
  fun h => Std.lt_irrefl (Std.lt_of_le_of_lt (Slice.Pos.le_endPos _) h)

@[simp]
theorem Pos.not_endPos_lt {s : String} {p : s.Pos} : ¬ s.endPos < p :=
  fun h => Std.lt_irrefl (Std.lt_of_le_of_lt (Pos.le_endPos _) h)

theorem Pos.ne_endPos_of_lt {s : String} {p q : s.Pos} : p < q → p ≠ s.endPos := by
  rintro h rfl
  simp at h

@[simp]
theorem Slice.Pos.le_next {s : Slice} {p : s.Pos} {h} : p ≤ p.next h :=
  Std.le_of_lt (by simp)

@[simp]
theorem Pos.le_next {s : String} {p : s.Pos} {h} : p ≤ p.next h :=
  Std.le_of_lt (by simp)

@[simp]
theorem Slice.Pos.next_ne_startPos {s : Slice} {p : s.Pos} {h} :
    p.next h ≠ s.startPos :=
  ne_startPos_of_lt lt_next

theorem Slice.Pos.ofSliceTo_lt_ofSliceTo_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceTo p).Pos} : Slice.Pos.ofSliceTo q < Slice.Pos.ofSliceTo r ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff]

theorem Slice.Pos.ofSliceTo_le_ofSliceTo_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceTo p).Pos} : Slice.Pos.ofSliceTo q ≤ Slice.Pos.ofSliceTo r ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff]

@[simp]
theorem Slice.Pos.sliceFrom_lt_sliceFrom_iff {s : Slice} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceFrom p₀ q h₁ < Pos.sliceFrom p₀ r h₂ ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff, Slice.Pos.le_iff, Pos.Raw.le_iff] at h₁ h₂ ⊢
  omega

@[simp]
theorem Slice.Pos.sliceFrom_le_sliceFrom_iff {s : Slice} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceFrom p₀ q h₁ ≤ Pos.sliceFrom p₀ r h₂ ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff] at h₁ h₂ ⊢
  omega

@[simp]
theorem Pos.sliceFrom_lt_sliceFrom_iff {s : String} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceFrom p₀ q h₁ < Pos.sliceFrom p₀ r h₂ ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.lt_iff, Pos.Raw.lt_iff, Pos.le_iff, Pos.Raw.le_iff] at h₁ h₂ ⊢
  omega

@[simp]
theorem Pos.sliceFrom_le_sliceFrom_iff {s : String} {p₀ : s.Pos} {q r : s.Pos} {h₁ h₂} :
    Pos.sliceFrom p₀ q h₁ ≤ Pos.sliceFrom p₀ r h₂ ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.le_iff, Pos.Raw.le_iff] at h₁ h₂ ⊢
  omega

theorem Slice.Pos.ofSliceFrom_lt_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    Pos.ofSliceFrom p < q ↔ ∃ h, p < Slice.Pos.sliceFrom p₀ q h := by
  refine ⟨fun h => ⟨Std.le_of_lt (Std.lt_of_le_of_lt Pos.le_ofSliceFrom h), ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceFrom_ofSliceFrom (p := p)]
    rwa [Pos.sliceFrom_lt_sliceFrom_iff]
  · simp +singlePass only [← Pos.ofSliceFrom_sliceFrom (h := h)]
    rwa [Pos.ofSliceFrom_lt_ofSliceFrom_iff]

theorem Slice.Pos.le_ofSliceFrom_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    q ≤ Pos.ofSliceFrom p ↔ ∀ h, Slice.Pos.sliceFrom p₀ q h ≤ p := by
  simp [← Std.not_lt, Pos.ofSliceFrom_lt_iff]

theorem Slice.Pos.ofSliceFrom_le_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    Pos.ofSliceFrom p ≤ q ↔ ∃ h, p ≤ Slice.Pos.sliceFrom p₀ q h := by
  refine ⟨fun h => ⟨Std.le_trans Pos.le_ofSliceFrom h, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceFrom_ofSliceFrom (p := p)]
    rwa [Pos.sliceFrom_le_sliceFrom_iff]
  · simp +singlePass only [← Pos.ofSliceFrom_sliceFrom (h := h)]
    rwa [Pos.ofSliceFrom_le_ofSliceFrom_iff]

theorem Slice.Pos.lt_ofSliceFrom_iff {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    q < Pos.ofSliceFrom p ↔ ∀ h, Slice.Pos.sliceFrom p₀ q h < p := by
  simp [← Std.not_le, Pos.ofSliceFrom_le_iff]

theorem Pos.ofSliceFrom_lt_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    Pos.ofSliceFrom p < q ↔ ∃ h, p < Pos.sliceFrom p₀ q h := by
  refine ⟨fun h => ⟨Std.le_of_lt (Std.lt_of_le_of_lt Pos.le_ofSliceFrom h), ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceFrom_ofSliceFrom (p := p)]
    rwa [Pos.sliceFrom_lt_sliceFrom_iff]
  · simp +singlePass only [← Pos.ofSliceFrom_sliceFrom (h := h)]
    rwa [Pos.ofSliceFrom_lt_ofSliceFrom_iff]

theorem Pos.le_ofSliceFrom_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    q ≤ Pos.ofSliceFrom p ↔ ∀ h, Pos.sliceFrom p₀ q h ≤ p := by
  simp [← Std.not_lt, Pos.ofSliceFrom_lt_iff]

theorem Pos.ofSliceFrom_le_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    Pos.ofSliceFrom p ≤ q ↔ ∃ h, p ≤ Pos.sliceFrom p₀ q h := by
  refine ⟨fun h => ⟨Std.le_trans Pos.le_ofSliceFrom h, ?_⟩, fun ⟨h, h'⟩ => ?_⟩
  · simp +singlePass only [← Pos.sliceFrom_ofSliceFrom (p := p)]
    rwa [Pos.sliceFrom_le_sliceFrom_iff]
  · simp +singlePass only [← Pos.ofSliceFrom_sliceFrom (h := h)]
    rwa [Pos.ofSliceFrom_le_ofSliceFrom_iff]

theorem Pos.lt_ofSliceFrom_iff {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {q : s.Pos} :
    q < Pos.ofSliceFrom p ↔ ∀ h, Pos.sliceFrom p₀ q h < p := by
  simp [← Std.not_le, Pos.ofSliceFrom_le_iff]

theorem Slice.Pos.ofSliceFrom_next {s : Slice} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {h} :
    Pos.ofSliceFrom (p.next h) = (Pos.ofSliceFrom p).next (by simpa [← Pos.ofSliceFrom_inj] using h) := by
  rw [eq_comm, Pos.next_eq_iff]
  simp only [Pos.ofSliceFrom_lt_ofSliceFrom_iff, Pos.lt_next, Pos.ofSliceFrom_le_iff,
    Pos.next_le_iff_lt, true_and]
  simp [Pos.ofSliceFrom_lt_iff]

theorem Pos.ofSliceFrom_next {s : String} {p₀ : s.Pos} {p : (s.sliceFrom p₀).Pos} {h} :
    Pos.ofSliceFrom (p.next h) = (Pos.ofSliceFrom p).next (by simpa [← Pos.ofSliceFrom_inj] using h) := by
  rw [eq_comm, Pos.next_eq_iff]
  simp only [Pos.ofSliceFrom_lt_ofSliceFrom_iff, Slice.Pos.lt_next, Pos.ofSliceFrom_le_iff,
    Slice.Pos.next_le_iff_lt, true_and]
  simp [Pos.ofSliceFrom_lt_iff]

@[simp]
theorem Slice.Pos.offset_le_rawEndPos {s : Slice} {p : s.Pos} :
    p.offset ≤ s.rawEndPos :=
  p.isValidForSlice.le_rawEndPos

@[simp]
theorem Pos.offset_le_rawEndPos {s : String} {p : s.Pos} :
    p.offset ≤ s.rawEndPos :=
  p.isValid.le_rawEndPos

@[simp]
theorem Slice.Pos.byteIdx_offset_le_utf8ByteSize {s : Slice} {p : s.Pos} :
    p.offset.byteIdx ≤ s.utf8ByteSize := by
  simp [← byteIdx_rawEndPos, ← Pos.Raw.le_iff]

@[simp]
theorem Pos.byteIdx_offset_le_utf8ByteSize {s : String} {p : s.Pos} :
    p.offset.byteIdx ≤ s.utf8ByteSize := by
  simp [← byteIdx_rawEndPos, ← Pos.Raw.le_iff]

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
