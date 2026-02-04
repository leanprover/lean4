/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import all Init.Data.String.Defs
import Init.Data.String.Lemmas.Order
import Init.Data.String.Lemmas.Basic
import Init.Data.String.OrderInstances
import Init.Grind

public section

namespace String

namespace Slice

theorem isEmpty_eq {s : Slice} : s.isEmpty = (s.utf8ByteSize == 0) :=
  (rfl)

theorem isEmpty_iff {s : Slice} :
    s.isEmpty ↔ s.utf8ByteSize = 0 := by
  simp [Slice.isEmpty_eq]

theorem startPos_eq_endPos_iff {s : Slice} :
    s.startPos = s.endPos ↔ s.isEmpty := by
  rw [eq_comm]
  simp [Slice.Pos.ext_iff, Pos.Raw.ext_iff, Slice.isEmpty_iff]

theorem startPos_ne_endPos_iff {s : Slice} :
    s.startPos ≠ s.endPos ↔ s.isEmpty = false := by
  simp [Slice.startPos_eq_endPos_iff]

theorem startPos_ne_endPos {s : Slice} : s.isEmpty = false → s.startPos ≠ s.endPos :=
  Slice.startPos_ne_endPos_iff.2

theorem isEmpty_iff_forall_eq {s : Slice} :
    s.isEmpty ↔ ∀ (p q : s.Pos), p = q := by
  rw [← Slice.startPos_eq_endPos_iff]
  refine ⟨fun h p q => ?_, fun h => h _ _⟩
  apply Std.le_antisymm
  · apply Std.le_trans (Pos.le_endPos _) (h ▸ Pos.startPos_le _)
  · apply Std.le_trans (Pos.le_endPos _) (h ▸ Pos.startPos_le _)

theorem isEmpty_eq_false_of_lt {s : Slice} {p q : s.Pos} :
    p < q → s.isEmpty = false := by
  rw [← Decidable.not_imp_not]
  simp
  rw [Slice.isEmpty_iff_forall_eq]
  intro h
  cases h p q
  apply Std.lt_irrefl

@[simp]
theorem isEmpty_sliceFrom {s : Slice} {p : s.Pos} :
    (s.sliceFrom p).isEmpty ↔ p = s.endPos := by
  simp [← startPos_eq_endPos_iff, ← Pos.ofSliceFrom_inj]

@[simp]
theorem isEmpty_sliceFrom_eq_false_iff {s : Slice} {p : s.Pos} :
    (s.sliceFrom p).isEmpty = false ↔ p ≠ s.endPos :=
  Decidable.not_iff_not.1 (by simp)

@[simp]
theorem isEmpty_sliceTo {s : Slice} {p : s.Pos} :
    (s.sliceTo p).isEmpty ↔ p = s.startPos := by
  simp [← startPos_eq_endPos_iff, eq_comm (a := p), ← Pos.ofSliceTo_inj]

@[simp]
theorem isEmpty_sliceTo_eq_false_iff {s : Slice} {p : s.Pos} :
    (s.sliceTo p).isEmpty = false ↔ p ≠ s.startPos :=
  Decidable.not_iff_not.1 (by simp)

end Slice

theorem isEmpty_eq_utf8ByteSize_beq_zero {s : String} : s.isEmpty = (s.utf8ByteSize == 0) :=
  (rfl)

theorem isEmpty_iff_utf8ByteSize_eq_zero {s : String} : s.isEmpty ↔ s.utf8ByteSize = 0 := by
  simp [isEmpty_eq_utf8ByteSize_beq_zero]

@[simp]
theorem isEmpty_iff {s : String} : s.isEmpty ↔ s = "" := by
  simp [isEmpty_iff_utf8ByteSize_eq_zero]

theorem startPos_ne_endPos_iff {s : String} : s.startPos ≠ s.endPos ↔ s ≠ "" := by
  simp

theorem startPos_ne_endPos {s : String} : s ≠ "" → s.startPos ≠ s.endPos :=
  startPos_ne_endPos_iff.2

@[simp]
theorem isEmpty_toSlice {s : String} : s.toSlice.isEmpty = s.isEmpty := by
  simp [isEmpty_eq_utf8ByteSize_beq_zero, Slice.isEmpty_eq]

theorem isEmpty_toSlice_iff {s : String} : s.toSlice.isEmpty ↔ s = "" := by
  simp

theorem eq_empty_iff_forall_eq {s : String} : s = "" ↔ ∀ (p q : s.Pos), p = q := by
  rw [← isEmpty_toSlice_iff, Slice.isEmpty_iff_forall_eq]
  exact ⟨fun h p q => by simpa [Pos.toSlice_inj] using h p.toSlice q.toSlice,
    fun h p q => by simpa [Pos.ofToSlice_inj] using h (Pos.ofToSlice p) (Pos.ofToSlice q)⟩

theorem ne_empty_of_lt {s : String} {p q : s.Pos} :
    p < q → s ≠ "" := by
  rw [← Pos.toSlice_lt_toSlice_iff, ne_eq, ← isEmpty_toSlice_iff, Bool.not_eq_true]
  exact Slice.isEmpty_eq_false_of_lt

@[simp]
theorem isEmpty_sliceFrom {s : String} {p : s.Pos} :
    (s.sliceFrom p).isEmpty ↔ p = s.endPos := by
  simp [← Slice.startPos_eq_endPos_iff, ← Pos.ofSliceFrom_inj]

@[simp]
theorem isEmpty_sliceFrom_eq_false_iff {s : String} {p : s.Pos} :
    (s.sliceFrom p).isEmpty = false ↔ p ≠ s.endPos :=
  Decidable.not_iff_not.1 (by simp)

@[simp]
theorem isEmpty_sliceTo {s : String} {p : s.Pos} :
    (s.sliceTo p).isEmpty ↔ p = s.startPos := by
  simp [← Slice.startPos_eq_endPos_iff, eq_comm (a := p), ← Pos.ofSliceTo_inj]

@[simp]
theorem isEmpty_sliceTo_eq_false_iff {s : String} {p : s.Pos} :
    (s.sliceTo p).isEmpty = false ↔ p ≠ s.startPos :=
  Decidable.not_iff_not.1 (by simp)

end String
