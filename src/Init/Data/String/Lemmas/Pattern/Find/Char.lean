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
import Init.Data.String.OrderInstances

namespace String.Slice

theorem find?_char_eq_some_iff {c : Char} {s : Slice} {pos : s.Pos} :
    s.find? c = some pos ↔
      ∃ h, pos.get h = c ∧ ∀ pos', (h' : pos' < pos) → pos'.get (Pos.ne_endPos_of_lt h') ≠ c := by
  grind [Pattern.Model.find?_eq_some_iff, Pattern.Model.Char.matchesAt_iff]

@[simp]
theorem contains_char_eq {c : Char} {s : Slice} : s.contains c = decide (c ∈ s.copy.toList) := by
  rw [Bool.eq_iff_iff, Pattern.Model.contains_eq_true_iff]
  simp [Pattern.Model.Char.matchesAt_iff, mem_toList_copy_iff_exists_get]

theorem find?_char_eq_some_iff_splits {c : Char} {s : Slice} {pos : s.Pos} :
    s.find? c = some pos ↔ ∃ t u, pos.Splits t (singleton c ++ u) ∧ c ∉ t.toList := by
  rw [find?_char_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨h, hget, hmin⟩
    refine ⟨_, _, hget ▸ pos.splits_next_right h, fun hmem => ?_⟩
    obtain ⟨pos', hlt, hpget⟩ := (hget ▸ pos.splits_next_right h).mem_toList_left_iff.mp hmem
    exact absurd hpget (hmin _ hlt)
  · rintro ⟨t, u, hs, hnotin⟩
    have hne := hs.ne_endPos_of_singleton
    exact ⟨hne, (singleton_append_inj.mp (hs.eq_right (pos.splits_next_right hne))).1.symm,
      fun pos' hlt hget => hnotin (hs.mem_toList_left_iff.mpr ⟨pos', hlt, hget⟩)⟩

theorem Pos.find?_char_eq_some_iff {c : Char} {s : Slice} {pos pos' : s.Pos} :
    pos.find? c = some pos' ↔
      pos ≤ pos' ∧ (∃ h, pos'.get h = c) ∧
        ∀ pos'', pos ≤ pos'' → (h' : pos'' < pos') → pos''.get (Pos.ne_endPos_of_lt h') ≠ c := by
  grind [Pattern.Model.posFind?_eq_some_iff, Pattern.Model.Char.matchesAt_iff]

theorem Pos.find?_char_eq_some_iff_splits {c : Char} {s : Slice} {pos : s.Pos}
    {t u : String} (hs : pos.Splits t u) {pos' : s.Pos} :
    pos.find? c = some pos' ↔ ∃ v w, pos'.Splits (t ++ v) (singleton c ++ w) ∧ c ∉ v.toList := by
  rw [Pos.find?_char_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨hle, ⟨hne, hget⟩, hmin⟩
    have hsplit := hget ▸ pos'.splits_next_right hne
    obtain ⟨v, hv1, hv2⟩ := (hs.le_iff_exists_eq_append hsplit).mp hle
    refine ⟨v, _, hsplit.of_eq hv1 rfl, fun hmem => ?_⟩
    obtain ⟨_, hcopy⟩ :=
      Slice.copy_slice_eq_iff_splits.mpr ⟨t, _, hs.of_eq rfl hv2, hsplit.of_eq hv1 rfl⟩
    rw [← hcopy] at hmem
    obtain ⟨p, hp, hpget⟩ := mem_toList_copy_iff_exists_get.mp hmem
    have hlt : Pos.ofSlice p < pos' := by
      simpa [← Slice.Pos.lt_endPos_iff, ← Pos.ofSlice_lt_ofSlice_iff] using hp
    exact absurd (Pos.get_eq_get_ofSlice ▸ hpget) (hmin _ Pos.le_ofSlice hlt)
  · rintro ⟨v, w, hsplit, hnotin⟩
    have hne := hsplit.ne_endPos_of_singleton
    have hu : u = v ++ (singleton c ++ w) :=
      append_right_inj t |>.mp (hs.eq_append.symm.trans (by rw [hsplit.eq_append, append_assoc]))
    have hle : pos ≤ pos' := (hs.le_iff_exists_eq_append hsplit).mpr ⟨v, rfl, hu⟩
    refine ⟨hle,
      ⟨hne, (singleton_append_inj.mp (hsplit.eq_right (pos'.splits_next_right hne))).1.symm⟩,
      fun pos'' hle' hlt hget => hnotin ?_⟩
    obtain ⟨_, hcopy⟩ :=
      Slice.copy_slice_eq_iff_splits.mpr ⟨t, _, hs.of_eq rfl hu, hsplit⟩
    rw [← hcopy]
    exact mem_toList_copy_iff_exists_get.mpr
      ⟨pos''.slice pos pos' hle' (Std.le_of_lt hlt),
       fun h => Std.ne_of_lt hlt
         (by rw [← Slice.Pos.ofSlice_slice (h₁ := hle') (h₂ := Std.le_of_lt hlt), h,
                  Slice.Pos.ofSlice_endPos]),
       by rw [Slice.Pos.get_eq_get_ofSlice]
          simp [Slice.Pos.ofSlice_slice]
          exact hget⟩

theorem Pos.find?_char_eq_none_iff {c : Char} {s : Slice} {pos : s.Pos} :
    pos.find? c = none ↔ ∀ pos', pos ≤ pos' → (h : pos' ≠ s.endPos) → pos'.get h ≠ c := by
  grind [Pattern.Model.posFind?_eq_none_iff, Pattern.Model.Char.matchesAt_iff]

theorem Pos.find?_char_eq_none_iff_not_mem_of_splits {c : Char} {s : Slice} {pos : s.Pos}
    {t u : String} (hs : pos.Splits t u) :
    pos.find? c = none ↔ c ∉ u.toList := by
  simp [Pos.find?_char_eq_none_iff, hs.mem_toList_right_iff]

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

theorem Pos.find?_char_eq_some_iff_splits {c : Char} {s : String} {pos : s.Pos}
    {t u : String} (hs : pos.Splits t u) {pos' : s.Pos} :
    pos.find? c = some pos' ↔ ∃ v w, pos'.Splits (t ++ v) (singleton c ++ w) ∧ c ∉ v.toList := by
  simp only [Pos.find?_eq_find?_toSlice, Option.map_eq_some_iff,
    Slice.Pos.find?_char_eq_some_iff_splits (Pos.splits_toSlice_iff.mpr hs)]
  constructor
  · rintro ⟨q, ⟨v, w, hsplit, hnotin⟩, rfl⟩
    exact ⟨v, w, Slice.Pos.splits_ofToSlice_iff.mpr hsplit, hnotin⟩
  · rintro ⟨v, w, hsplit, hnotin⟩
    exact ⟨pos'.toSlice, ⟨v, w, Pos.splits_toSlice_iff.mpr hsplit, hnotin⟩, by simp⟩

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

theorem Pos.find?_char_eq_none_iff_not_mem_of_splits {c : Char} {s : String} {pos : s.Pos}
    {t u : String} (hs : pos.Splits t u) :
    pos.find? c = none ↔ c ∉ u.toList := by
  rw [Pos.find?_eq_find?_toSlice, Option.map_eq_none_iff]
  exact Slice.Pos.find?_char_eq_none_iff_not_mem_of_splits (Pos.splits_toSlice_iff.mpr hs)

theorem Pos.find?_char_eq_find?_beq {c : Char} {s : String} {pos : s.Pos} :
    pos.find? c = pos.find? (· == c) := by
  simp only [Pos.find?_eq_find?_toSlice, Slice.Pos.find?_char_eq_find?_beq]

theorem find?_char_eq_find?_beq {c : Char} {s : String} :
    s.find? c = s.find? (· == c) := by
  simp only [find?_eq_find?_toSlice, Slice.find?_char_eq_find?_beq]

theorem contains_char_eq_contains_beq {c : Char} {s : String} :
    s.contains c = s.contains (· == c) := by
  simp only [contains_eq_contains_toSlice, Slice.contains_char_eq_contains_beq]

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

theorem find?_char_eq_some_iff_splits {c : Char} {s : String} {pos : s.Pos} :
    s.find? c = some pos ↔ ∃ t u, pos.Splits t (singleton c ++ u) ∧ c ∉ t.toList := by
  simp only [find?_eq_find?_toSlice, Option.map_eq_some_iff,
    Slice.find?_char_eq_some_iff_splits]
  constructor
  · rintro ⟨q, ⟨t, u, hsplit, hnotin⟩, rfl⟩
    exact ⟨t, u, Slice.Pos.splits_ofToSlice_iff.mpr hsplit, hnotin⟩
  · rintro ⟨t, u, hsplit, hnotin⟩
    exact ⟨pos.toSlice, ⟨t, u, Pos.splits_toSlice_iff.mpr hsplit, hnotin⟩, by simp⟩

@[simp]
theorem contains_char_eq {c : Char} {s : String} : s.contains c = decide (c ∈ s.toList) := by
  simp [contains_eq_contains_toSlice, Slice.contains_char_eq, copy_toSlice]

end String
