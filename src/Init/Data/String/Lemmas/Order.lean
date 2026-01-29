/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Basic
import Init.Data.String.Grind
import Init.Data.String.Lemmas.Basic

public section

namespace Std

theorem lt_irrefl {α : Type u} [LT α] [Std.Irrefl (α := α) (· < ·)] {a : α} : ¬ a < a :=
  Std.Irrefl.irrefl a

theorem ne_of_lt {α : Type u} [LT α] [Std.Irrefl (α := α) (· < ·)] {a b : α} : a < b → a ≠ b :=
  fun h h' => absurd (h' ▸ h) (h' ▸ lt_irrefl)

end Std

namespace String

@[simp]
theorem Slice.Pos.next_le_iff_lt {s : Slice} {p q : s.Pos} {h} : p.next h ≤ q ↔ p < q :=
  ⟨fun h => Std.lt_of_lt_of_le lt_next h, next_le_of_lt⟩

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
  ⟨fun h => Std.le_antisymm (le_endPos _) h, by simp +contextual⟩

@[simp]
theorem Slice.Pos.not_lt_startPos {s : Slice} {p : s.Pos} : ¬ p < s.startPos :=
  fun h => Std.lt_irrefl (Std.lt_of_lt_of_le h (Slice.Pos.startPos_le _))

theorem Slice.Pos.ne_startPos_of_lt {s : Slice} {p q : s.Pos} : p < q → q ≠ s.startPos := by
  rintro h rfl
  simp at h

theorem Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceFrom p).Pos} : Slice.Pos.ofSliceFrom q < Slice.Pos.ofSliceFrom r ↔ q < r := by
  simp [Slice.Pos.lt_iff, Pos.Raw.lt_iff]

theorem Slice.Pos.ofSliceFrom_le_ofSliceFrom_iff {s : Slice} {p : s.Pos}
    {q r : (s.sliceFrom p).Pos} : Slice.Pos.ofSliceFrom q ≤ Slice.Pos.ofSliceFrom r ↔ q ≤ r := by
  simp [Slice.Pos.le_iff, Pos.Raw.le_iff]

end String
