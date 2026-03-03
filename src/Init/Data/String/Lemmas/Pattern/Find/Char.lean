/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
import Init.Data.String.Lemmas.Pattern.Find.Basic
import Init.Data.String.Lemmas.Pattern.Char
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Order
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Iterate
import Init.Grind
import Init.Data.Option.Lemmas

namespace String.Slice

theorem find?_char_eq_some_iff {c : Char} {s : Slice} {pos : s.Pos} :
    s.find? c = some pos ↔
      ∃ h, pos.get h = c ∧ ∀ pos', (h' : pos' < pos) → pos'.get (Pos.ne_endPos_of_lt h') ≠ c := by
  grind [Pattern.Model.find?_eq_some_iff, Pattern.Model.Char.matchesAt_iff]

@[simp]
theorem contains_char_eq {c : Char} {s : Slice} : s.contains c = decide (c ∈ s.copy.toList) := by
  rw [Bool.eq_iff_iff, Pattern.Model.contains_eq_true_iff]
  simp [Pattern.Model.Char.matchesAt_iff, mem_toList_copy_iff_exists_get]

theorem Pos.find?_char_eq_some_iff {c : Char} {s : Slice} {pos pos' : s.Pos} :
    pos.find? c = some pos' ↔
      pos ≤ pos' ∧ (∃ h, pos'.get h = c) ∧
        ∀ pos'', pos ≤ pos'' → (h' : pos'' < pos') → pos''.get (Pos.ne_endPos_of_lt h') ≠ c := by
  grind [Pattern.Model.posFind?_eq_some_iff, Pattern.Model.Char.matchesAt_iff]

theorem Pos.find?_char_eq_none_iff {c : Char} {s : Slice} {pos : s.Pos} :
    pos.find? c = none ↔ ∀ pos', pos ≤ pos' → (h : pos' ≠ s.endPos) → pos'.get h ≠ c := by
  grind [Pattern.Model.posFind?_eq_none_iff, Pattern.Model.Char.matchesAt_iff]

end Slice

theorem Pos.find?_char_eq_some_iff {c : Char} {s : String} {pos pos' : s.Pos} :
    pos.find? c = some pos' ↔
      pos ≤ pos' ∧ (∃ h, pos'.get h = c) ∧
        ∀ pos'', pos ≤ pos'' → (h' : pos'' < pos') → pos''.get (Pos.ne_endPos_of_lt h') ≠ c := by
  simp only [Pos.find?_eq_find?_toSlice, Option.map_eq_some_iff,
    Slice.Pos.find?_char_eq_some_iff, ne_eq, endPos_toSlice]
  refine ⟨?_, ?_⟩
  · rintro ⟨pos', ⟨h₁, ⟨h₂, rfl⟩, h₃⟩, rfl⟩
    refine ⟨by simpa [Pos.ofToSlice_le_iff] using h₁,
      ⟨by simpa [← Pos.ofToSlice_inj] using h₂, by simp [Pos.get_ofToSlice]⟩, ?_⟩
    intro pos'' h₄ h₅
    simpa using h₃ pos''.toSlice (by simpa [Pos.toSlice_le] using h₄) (by simpa using h₅)
  · rintro ⟨h₁, ⟨h₂, hget⟩, h₃⟩
    refine ⟨pos'.toSlice, ⟨by simpa [Pos.toSlice_le] using h₁,
      ⟨by simpa [← Pos.toSlice_inj] using h₂, by simpa using hget⟩, fun p hp₁ hp₂ => ?_⟩,
      by simp⟩
    simpa using h₃ (Pos.ofToSlice p)
      (by simpa [Pos.ofToSlice_le_iff] using hp₁) (by simpa using hp₂)

theorem Pos.find?_char_eq_none_iff {c : Char} {s : String} {pos : s.Pos} :
    pos.find? c = none ↔ ∀ pos', pos ≤ pos' → (h : pos' ≠ s.endPos) → pos'.get h ≠ c := by
  simp only [Pos.find?_eq_find?_toSlice, Option.map_eq_none_iff,
    Slice.Pos.find?_char_eq_none_iff, endPos_toSlice]
  refine ⟨?_, ?_⟩
  · intro h pos' h₁ h₂
    simpa [Pos.get_ofToSlice] using
      h pos'.toSlice (by simpa [Pos.toSlice_le] using h₁) (by simpa [← Pos.toSlice_inj] using h₂)
  · intro h pos' h₁ h₂
    simpa using h (Pos.ofToSlice pos')
      (by simpa [Pos.ofToSlice_le_iff] using h₁) (by simpa [← Pos.ofToSlice_inj] using h₂)

theorem find?_char_eq_some_iff {c : Char} {s : String} {pos : s.Pos} :
    s.find? c = some pos ↔
      ∃ h, pos.get h = c ∧ ∀ pos', (h' : pos' < pos) → pos'.get (Pos.ne_endPos_of_lt h') ≠ c := by
  simp only [find?_eq_find?_toSlice, Option.map_eq_some_iff, Slice.find?_char_eq_some_iff, ne_eq,
    endPos_toSlice, exists_and_right]
  refine ⟨?_, ?_⟩
  · rintro ⟨pos, ⟨⟨h, rfl⟩, h'⟩, rfl⟩
    refine ⟨⟨by simpa [← Pos.ofToSlice_inj] using h, by simp [Pos.get_ofToSlice]⟩, ?_⟩
    intro pos' hp
    simpa using h' pos'.toSlice hp
  · rintro ⟨⟨h, hget⟩, hmin⟩
    exact ⟨pos.toSlice, ⟨⟨by simpa [← Pos.toSlice_inj] using h, by simpa using hget⟩,
      fun pos' hp => by simpa using hmin (Pos.ofToSlice pos') hp⟩, by simp⟩

@[simp]
theorem contains_char_eq {c : Char} {s : String} : s.contains c = decide (c ∈ s.toList) := by
  simp [contains_eq_contains_toSlice, Slice.contains_char_eq, copy_toSlice]

end String
