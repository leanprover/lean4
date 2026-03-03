/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
import Init.Data.String.Lemmas.Pattern.Find.Basic
import Init.Data.String.Lemmas.Pattern.Pred
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Order
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Iterate
import Init.Grind
import Init.Data.Option.Lemmas

namespace String.Slice

theorem find?_bool_eq_some_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ h, p (pos.get h) ∧ ∀ pos', (h' : pos' < pos) → p (pos'.get (Pos.ne_endPos_of_lt h')) = false := by
  grind [Pattern.Model.find?_eq_some_iff, Pattern.Model.CharPred.matchesAt_iff]

theorem find?_prop_eq_some_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ h, p (pos.get h) ∧ ∀ pos', (h' : pos' < pos) → ¬ p (pos'.get (Pos.ne_endPos_of_lt h')) := by
  grind [Pattern.Model.find?_eq_some_iff, Pattern.Model.CharPred.Decidable.matchesAt_iff]

@[simp]
theorem contains_bool_eq {p : Char → Bool} {s : Slice} : s.contains p = s.copy.toList.any p := by
  rw [Bool.eq_iff_iff, Pattern.Model.contains_eq_true_iff]
  simp only [Pattern.Model.CharPred.matchesAt_iff, ne_eq, List.any_eq_true,
    mem_toList_copy_iff_exists_get]
  exact ⟨fun ⟨pos, h, hp⟩ => ⟨_, ⟨_, _, rfl⟩, hp⟩, fun ⟨_, ⟨p, h, h'⟩, hp⟩ => ⟨p, h, h' ▸ hp⟩⟩

@[simp]
theorem contains_prop_eq {p : Char → Prop} [DecidablePred p] {s : Slice} :
    s.contains p = s.copy.toList.any p := by
  rw [Bool.eq_iff_iff, Pattern.Model.contains_eq_true_iff]
  simp only [Pattern.Model.CharPred.Decidable.matchesAt_iff, ne_eq, List.any_eq_true,
    mem_toList_copy_iff_exists_get, decide_eq_true_eq]
  exact ⟨fun ⟨pos, h, hp⟩ => ⟨_, ⟨_, _, rfl⟩, hp⟩, fun ⟨_, ⟨p, h, h'⟩, hp⟩ => ⟨p, h, h' ▸ hp⟩⟩

theorem Pos.find?_bool_eq_some_iff {p : Char → Bool} {s : Slice} {pos pos' : s.Pos} :
    pos.find? p = some pos' ↔
      pos ≤ pos' ∧ (∃ h, p (pos'.get h)) ∧
        ∀ pos'', pos ≤ pos'' → (h' : pos'' < pos') →
          p (pos''.get (Pos.ne_endPos_of_lt h')) = false := by
  grind [Pattern.Model.posFind?_eq_some_iff, Pattern.Model.CharPred.matchesAt_iff]

theorem Pos.find?_bool_eq_none_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    pos.find? p = none ↔
      ∀ pos', pos ≤ pos' → (h : pos' ≠ s.endPos) → p (pos'.get h) = false := by
  grind [Pattern.Model.posFind?_eq_none_iff, Pattern.Model.CharPred.matchesAt_iff]

theorem Pos.find?_prop_eq_some_iff {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos pos' : s.Pos} :
    pos.find? p = some pos' ↔
      pos ≤ pos' ∧ (∃ h, p (pos'.get h)) ∧
        ∀ pos'', pos ≤ pos'' → (h' : pos'' < pos') →
          ¬ p (pos''.get (Pos.ne_endPos_of_lt h')) := by
  grind [Pattern.Model.posFind?_eq_some_iff, Pattern.Model.CharPred.Decidable.matchesAt_iff]

theorem Pos.find?_prop_eq_none_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    pos.find? p = none ↔
      ∀ pos', pos ≤ pos' → (h : pos' ≠ s.endPos) → ¬ p (pos'.get h) := by
  grind [Pattern.Model.posFind?_eq_none_iff, Pattern.Model.CharPred.Decidable.matchesAt_iff]

end String.Slice

namespace String

theorem Pos.find?_bool_eq_some_iff {p : Char → Bool} {s : String} {pos pos' : s.Pos} :
    pos.find? p = some pos' ↔
      pos ≤ pos' ∧ (∃ h, p (pos'.get h)) ∧
        ∀ pos'', pos ≤ pos'' → (h' : pos'' < pos') →
          p (pos''.get (Pos.ne_endPos_of_lt h')) = false := by
  simp only [Pos.find?_eq_find?_toSlice, Option.map_eq_some_iff,
    Slice.Pos.find?_bool_eq_some_iff, endPos_toSlice]
  refine ⟨?_, ?_⟩
  · rintro ⟨pos', ⟨h₁, ⟨h₂, hp⟩, h₃⟩, rfl⟩
    refine ⟨by simpa [Pos.ofToSlice_le_iff] using h₁,
      ⟨by simpa [← Pos.ofToSlice_inj] using h₂, by simpa [Pos.get_ofToSlice] using hp⟩, ?_⟩
    intro pos'' h₄ h₅
    simpa using h₃ pos''.toSlice (by simpa [Pos.toSlice_le] using h₄) (by simpa using h₅)
  · rintro ⟨h₁, ⟨h₂, hp⟩, h₃⟩
    refine ⟨pos'.toSlice, ⟨by simpa [Pos.toSlice_le] using h₁,
      ⟨by simpa [← Pos.toSlice_inj] using h₂, by simpa using hp⟩, fun p hp₁ hp₂ => ?_⟩,
      by simp⟩
    simpa using h₃ (Pos.ofToSlice p)
      (by simpa [Pos.ofToSlice_le_iff] using hp₁) (by simpa using hp₂)

theorem Pos.find?_bool_eq_none_iff {p : Char → Bool} {s : String} {pos : s.Pos} :
    pos.find? p = none ↔
      ∀ pos', pos ≤ pos' → (h : pos' ≠ s.endPos) → p (pos'.get h) = false := by
  simp only [Pos.find?_eq_find?_toSlice, Option.map_eq_none_iff,
    Slice.Pos.find?_bool_eq_none_iff, endPos_toSlice]
  refine ⟨?_, ?_⟩
  · intro h pos' h₁ h₂
    simpa [Pos.get_ofToSlice] using
      h pos'.toSlice (by simpa [Pos.toSlice_le] using h₁) (by simpa [← Pos.toSlice_inj] using h₂)
  · intro h pos' h₁ h₂
    simpa using h (Pos.ofToSlice pos')
      (by simpa [Pos.ofToSlice_le_iff] using h₁) (by simpa [← Pos.ofToSlice_inj] using h₂)

theorem Pos.find?_prop_eq_some_iff {p : Char → Prop} [DecidablePred p] {s : String}
    {pos pos' : s.Pos} :
    pos.find? p = some pos' ↔
      pos ≤ pos' ∧ (∃ h, p (pos'.get h)) ∧
        ∀ pos'', pos ≤ pos'' → (h' : pos'' < pos') →
          ¬ p (pos''.get (Pos.ne_endPos_of_lt h')) := by
  simp only [Pos.find?_eq_find?_toSlice, Option.map_eq_some_iff,
    Slice.Pos.find?_prop_eq_some_iff, endPos_toSlice]
  refine ⟨?_, ?_⟩
  · rintro ⟨pos', ⟨h₁, ⟨h₂, hp⟩, h₃⟩, rfl⟩
    refine ⟨by simpa [Pos.ofToSlice_le_iff] using h₁,
      ⟨by simpa [← Pos.ofToSlice_inj] using h₂, by simpa [Pos.get_ofToSlice] using hp⟩, ?_⟩
    intro pos'' h₄ h₅
    simpa using h₃ pos''.toSlice (by simpa [Pos.toSlice_le] using h₄) (by simpa using h₅)
  · rintro ⟨h₁, ⟨h₂, hp⟩, h₃⟩
    refine ⟨pos'.toSlice, ⟨by simpa [Pos.toSlice_le] using h₁,
      ⟨by simpa [← Pos.toSlice_inj] using h₂, by simpa using hp⟩, fun p hp₁ hp₂ => ?_⟩,
      by simp⟩
    simpa using h₃ (Pos.ofToSlice p)
      (by simpa [Pos.ofToSlice_le_iff] using hp₁) (by simpa using hp₂)

theorem Pos.find?_prop_eq_none_iff {p : Char → Prop} [DecidablePred p] {s : String}
    {pos : s.Pos} :
    pos.find? p = none ↔
      ∀ pos', pos ≤ pos' → (h : pos' ≠ s.endPos) → ¬ p (pos'.get h) := by
  simp only [Pos.find?_eq_find?_toSlice, Option.map_eq_none_iff,
    Slice.Pos.find?_prop_eq_none_iff, endPos_toSlice]
  refine ⟨?_, ?_⟩
  · intro h pos' h₁ h₂
    simpa [Pos.get_ofToSlice] using
      h pos'.toSlice (by simpa [Pos.toSlice_le] using h₁) (by simpa [← Pos.toSlice_inj] using h₂)
  · intro h pos' h₁ h₂
    simpa using h (Pos.ofToSlice pos')
      (by simpa [Pos.ofToSlice_le_iff] using h₁) (by simpa [← Pos.ofToSlice_inj] using h₂)

theorem find?_bool_eq_some_iff {p : Char → Bool} {s : String} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ h, p (pos.get h) ∧ ∀ pos', (h' : pos' < pos) → p (pos'.get (Pos.ne_endPos_of_lt h')) = false := by
  simp only [find?_eq_find?_toSlice, Option.map_eq_some_iff, Slice.find?_bool_eq_some_iff,
    endPos_toSlice, exists_and_right]
  refine ⟨?_, ?_⟩
  · rintro ⟨pos, ⟨⟨h, hp⟩, h'⟩, rfl⟩
    refine ⟨⟨by simpa [← Pos.ofToSlice_inj] using h, by simpa [Pos.get_ofToSlice] using hp⟩, ?_⟩
    intro pos' hp
    simpa using h' pos'.toSlice hp
  · rintro ⟨⟨h, hp⟩, hmin⟩
    exact ⟨pos.toSlice, ⟨⟨by simpa [← Pos.toSlice_inj] using h, by simpa using hp⟩,
      fun pos' hp => by simpa using hmin (Pos.ofToSlice pos') hp⟩, by simp⟩

theorem find?_prop_eq_some_iff {p : Char → Prop} [DecidablePred p] {s : String} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ h, p (pos.get h) ∧ ∀ pos', (h' : pos' < pos) → ¬ p (pos'.get (Pos.ne_endPos_of_lt h')) := by
  simp only [find?_eq_find?_toSlice, Option.map_eq_some_iff, Slice.find?_prop_eq_some_iff,
    endPos_toSlice, exists_and_right]
  refine ⟨?_, ?_⟩
  · rintro ⟨pos, ⟨⟨h, hp⟩, h'⟩, rfl⟩
    refine ⟨⟨by simpa [← Pos.ofToSlice_inj] using h, by simpa [Pos.get_ofToSlice] using hp⟩, ?_⟩
    intro pos' hp
    simpa using h' pos'.toSlice hp
  · rintro ⟨⟨h, hp⟩, hmin⟩
    exact ⟨pos.toSlice, ⟨⟨by simpa [← Pos.toSlice_inj] using h, by simpa using hp⟩,
      fun pos' hp => by simpa using hmin (Pos.ofToSlice pos') hp⟩, by simp⟩

@[simp]
theorem contains_bool_eq {p : Char → Bool} {s : String} : s.contains p = s.toList.any p := by
  simp [contains_eq_contains_toSlice, Slice.contains_bool_eq, copy_toSlice]

@[simp]
theorem contains_prop_eq {p : Char → Prop} [DecidablePred p] {s : String} :
    s.contains p = s.toList.any p := by
  simp [contains_eq_contains_toSlice, Slice.contains_prop_eq, copy_toSlice]

end String
