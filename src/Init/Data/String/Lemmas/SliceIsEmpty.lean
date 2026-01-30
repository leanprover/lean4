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
import Init.Data.String.Grind
import Init.Grind

public section

namespace String

theorem Slice.isEmpty_eq {s : Slice} : s.isEmpty = (s.utf8ByteSize == 0) :=
  (rfl)

theorem Slice.isEmpty_iff {s : Slice} :
    s.isEmpty ↔ s.utf8ByteSize = 0 := by
  simp [Slice.isEmpty_eq]

theorem Slice.startPos_eq_endPos_iff {s : Slice} :
    s.startPos = s.endPos ↔ s.isEmpty := by
  rw [eq_comm]
  simp [Slice.Pos.ext_iff, Pos.Raw.ext_iff, Slice.isEmpty_iff]

theorem Slice.startPos_ne_endPos_iff {s : Slice} :
    s.startPos ≠ s.endPos ↔ s.isEmpty = false := by
  simp [Slice.startPos_eq_endPos_iff]

theorem Slice.startPos_ne_endPos {s : Slice} : s.isEmpty = false → s.startPos ≠ s.endPos :=
  Slice.startPos_ne_endPos_iff.2

theorem Slice.isEmpty_iff_eq_endPos {s : Slice} :
    s.isEmpty ↔ ∀ (p q : s.Pos), p = q := by
  rw [← Slice.startPos_eq_endPos_iff]
  refine ⟨fun h p q => ?_, fun h => h _ _⟩
  apply Std.le_antisymm
  · apply Std.le_trans (Pos.le_endPos _) (h ▸ Pos.startPos_le _)
  · apply Std.le_trans (Pos.le_endPos _) (h ▸ Pos.startPos_le _)

theorem Slice.isEmpty_eq_false_of_lt {s : Slice} {p q : s.Pos} :
    p < q → s.isEmpty = false := by
  rw [← Decidable.not_imp_not]
  simp
  rw [Slice.isEmpty_iff_eq_endPos]
  intro h
  cases h p q
  apply Std.lt_irrefl

@[simp]
theorem Slice.isEmpty_sliceFrom {s : Slice} {p : s.Pos} :
    (s.sliceFrom p).isEmpty ↔ p = s.endPos := by
  simp [← startPos_eq_endPos_iff, ← Pos.ofSliceFrom_inj]

@[simp]
theorem Slice.isEmpty_sliceFrom_eq_false_iff {s : Slice} {p : s.Pos} :
    (s.sliceFrom p).isEmpty = false ↔ p ≠ s.endPos :=
  Decidable.not_iff_not.1 (by simp)

end String
