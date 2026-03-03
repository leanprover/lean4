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
import Init.Data.String.OrderInstances

namespace String.Slice

theorem find?_bool_eq_some_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ h, p (pos.get h) ∧ ∀ pos', (h' : pos' < pos) → p (pos'.get (Pos.ne_endPos_of_lt h')) = false := by
  grind [Pattern.Model.find?_eq_some_iff, Pattern.Model.CharPred.matchesAt_iff]

theorem find?_prop_eq_some_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ h, p (pos.get h) ∧ ∀ pos', (h' : pos' < pos) → ¬ p (pos'.get (Pos.ne_endPos_of_lt h')) := by
  grind [Pattern.Model.find?_eq_some_iff, Pattern.Model.CharPred.Decidable.matchesAt_iff]

theorem find?_bool_eq_some_iff_splits {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ t c u, pos.Splits t (singleton c ++ u) ∧ p c ∧ ∀ d ∈ t.toList, p d = false := by
  rw [find?_bool_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨h, hp, hmin⟩
    exact ⟨_, _, _, pos.splits_next_right h, hp, fun d hd => by
      obtain ⟨pos', hlt, hpget⟩ := (pos.splits_next_right h).mem_toList_left_iff.mp hd
      subst hpget; exact hmin _ hlt⟩
  · rintro ⟨t, c, u, hs, hpc, hmin⟩
    have hne := hs.ne_endPos_of_singleton
    refine ⟨hne, ?_, fun pos' hlt => hmin _ (hs.mem_toList_left_iff.mpr ⟨pos', hlt, rfl⟩)⟩
    rw [(singleton_append_inj.mp (hs.eq_right (pos.splits_next_right hne))).1.symm]
    exact hpc

theorem find?_prop_eq_some_iff_splits {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ t c u, pos.Splits t (singleton c ++ u) ∧ p c ∧ ∀ d ∈ t.toList, ¬ p d := by
  rw [find?_prop_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨h, hp, hmin⟩
    exact ⟨_, _, _, pos.splits_next_right h, hp, fun d hd => by
      obtain ⟨pos', hlt, hpget⟩ := (pos.splits_next_right h).mem_toList_left_iff.mp hd
      subst hpget; exact hmin _ hlt⟩
  · rintro ⟨t, c, u, hs, hpc, hmin⟩
    have hne := hs.ne_endPos_of_singleton
    refine ⟨hne, ?_, fun pos' hlt => hmin _ (hs.mem_toList_left_iff.mpr ⟨pos', hlt, rfl⟩)⟩
    rw [(singleton_append_inj.mp (hs.eq_right (pos.splits_next_right hne))).1.symm]
    exact hpc

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

theorem Pos.find?_bool_eq_some_iff_splits {p : Char → Bool} {s : Slice} {pos : s.Pos}
    {t u : String} (hs : pos.Splits t u) {pos' : s.Pos} :
    pos.find? p = some pos' ↔
      ∃ v c w, pos'.Splits (t ++ v) (singleton c ++ w) ∧ p c ∧
        ∀ d ∈ v.toList, p d = false := by
  rw [Pos.find?_bool_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨hle, ⟨hne, hp⟩, hmin⟩
    have hsplit := pos'.splits_next_right hne
    obtain ⟨v, hv1, hv2⟩ := (hs.le_iff_exists_eq_append hsplit).mp hle
    refine ⟨v, pos'.get hne, _, hsplit.of_eq hv1 rfl, hp, fun d hd => ?_⟩
    obtain ⟨_, hcopy⟩ :=
      Slice.copy_slice_eq_iff_splits.mpr ⟨t, _, hs.of_eq rfl hv2, hsplit.of_eq hv1 rfl⟩
    rw [← hcopy] at hd
    obtain ⟨q, hq, hqget⟩ := mem_toList_copy_iff_exists_get.mp hd
    have hlt : Pos.ofSlice q < pos' := by
      simpa [← Slice.Pos.lt_endPos_iff, ← Pos.ofSlice_lt_ofSlice_iff] using hq
    subst hqget; rw [Slice.Pos.get_eq_get_ofSlice]; exact hmin _ Pos.le_ofSlice hlt
  · rintro ⟨v, c, w, hsplit, hpc, hmin⟩
    have hne := hsplit.ne_endPos_of_singleton
    have hu : u = v ++ (singleton c ++ w) :=
      append_right_inj t |>.mp (hs.eq_append.symm.trans (by rw [hsplit.eq_append, append_assoc]))
    have hle : pos ≤ pos' := (hs.le_iff_exists_eq_append hsplit).mpr ⟨v, rfl, hu⟩
    refine ⟨hle, ⟨hne, ?_⟩, fun pos'' hle' hlt => hmin _ ?_⟩
    · rw [(singleton_append_inj.mp (hsplit.eq_right (pos'.splits_next_right hne))).1.symm]
      exact hpc
    · obtain ⟨_, hcopy⟩ :=
        Slice.copy_slice_eq_iff_splits.mpr ⟨t, _, hs.of_eq rfl hu, hsplit⟩
      rw [← hcopy]
      exact mem_toList_copy_iff_exists_get.mpr
        ⟨pos''.slice pos pos' hle' (Std.le_of_lt hlt),
         fun h => Std.ne_of_lt hlt
           (by rw [← Slice.Pos.ofSlice_slice (h₁ := hle') (h₂ := Std.le_of_lt hlt), h,
                    Slice.Pos.ofSlice_endPos]),
         by rw [Slice.Pos.get_eq_get_ofSlice]
            simp [Slice.Pos.ofSlice_slice]⟩

theorem Pos.find?_bool_eq_none_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    pos.find? p = none ↔
      ∀ pos', pos ≤ pos' → (h : pos' ≠ s.endPos) → p (pos'.get h) = false := by
  grind [Pattern.Model.posFind?_eq_none_iff, Pattern.Model.CharPred.matchesAt_iff]

theorem Pos.find?_bool_eq_none_iff_of_splits {p : Char → Bool} {s : Slice} {pos : s.Pos}
    {t u : String} (hs : pos.Splits t u) :
    pos.find? p = none ↔ ∀ c ∈ u.toList, p c = false := by
  rw [Pos.find?_bool_eq_none_iff]
  constructor
  · intro h c hc
    obtain ⟨pos', hle, hne, hget⟩ := hs.mem_toList_right_iff.mp hc
    subst hget; exact h pos' hle hne
  · intro h pos' hle hne
    exact h _ (hs.mem_toList_right_iff.mpr ⟨pos', hle, hne, rfl⟩)

theorem Pos.find?_prop_eq_some_iff {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos pos' : s.Pos} :
    pos.find? p = some pos' ↔
      pos ≤ pos' ∧ (∃ h, p (pos'.get h)) ∧
        ∀ pos'', pos ≤ pos'' → (h' : pos'' < pos') →
          ¬ p (pos''.get (Pos.ne_endPos_of_lt h')) := by
  grind [Pattern.Model.posFind?_eq_some_iff, Pattern.Model.CharPred.Decidable.matchesAt_iff]

theorem Pos.find?_prop_eq_some_iff_splits {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} {t u : String} (hs : pos.Splits t u) {pos' : s.Pos} :
    pos.find? p = some pos' ↔
      ∃ v c w, pos'.Splits (t ++ v) (singleton c ++ w) ∧ p c ∧ ∀ d ∈ v.toList, ¬ p d := by
  rw [Pos.find?_prop_eq_some_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨hle, ⟨hne, hp⟩, hmin⟩
    have hsplit := pos'.splits_next_right hne
    obtain ⟨v, hv1, hv2⟩ := (hs.le_iff_exists_eq_append hsplit).mp hle
    refine ⟨v, pos'.get hne, _, hsplit.of_eq hv1 rfl, hp, fun d hd => ?_⟩
    obtain ⟨_, hcopy⟩ :=
      Slice.copy_slice_eq_iff_splits.mpr ⟨t, _, hs.of_eq rfl hv2, hsplit.of_eq hv1 rfl⟩
    rw [← hcopy] at hd
    obtain ⟨q, hq, hqget⟩ := mem_toList_copy_iff_exists_get.mp hd
    have hlt : Pos.ofSlice q < pos' := by
      simpa [← Slice.Pos.lt_endPos_iff, ← Pos.ofSlice_lt_ofSlice_iff] using hq
    subst hqget; rw [Slice.Pos.get_eq_get_ofSlice]; exact hmin _ Pos.le_ofSlice hlt
  · rintro ⟨v, c, w, hsplit, hpc, hmin⟩
    have hne := hsplit.ne_endPos_of_singleton
    have hu : u = v ++ (singleton c ++ w) :=
      append_right_inj t |>.mp (hs.eq_append.symm.trans (by rw [hsplit.eq_append, append_assoc]))
    have hle : pos ≤ pos' := (hs.le_iff_exists_eq_append hsplit).mpr ⟨v, rfl, hu⟩
    refine ⟨hle, ⟨hne, ?_⟩, fun pos'' hle' hlt => hmin _ ?_⟩
    · rw [(singleton_append_inj.mp (hsplit.eq_right (pos'.splits_next_right hne))).1.symm]
      exact hpc
    · obtain ⟨_, hcopy⟩ :=
        Slice.copy_slice_eq_iff_splits.mpr ⟨t, _, hs.of_eq rfl hu, hsplit⟩
      rw [← hcopy]
      exact mem_toList_copy_iff_exists_get.mpr
        ⟨pos''.slice pos pos' hle' (Std.le_of_lt hlt),
         fun h => Std.ne_of_lt hlt
           (by rw [← Slice.Pos.ofSlice_slice (h₁ := hle') (h₂ := Std.le_of_lt hlt), h,
                    Slice.Pos.ofSlice_endPos]),
         by rw [Slice.Pos.get_eq_get_ofSlice]
            simp [Slice.Pos.ofSlice_slice]⟩

theorem Pos.find?_prop_eq_none_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    pos.find? p = none ↔
      ∀ pos', pos ≤ pos' → (h : pos' ≠ s.endPos) → ¬ p (pos'.get h) := by
  grind [Pattern.Model.posFind?_eq_none_iff, Pattern.Model.CharPred.Decidable.matchesAt_iff]

theorem Pos.find?_prop_eq_none_iff_of_splits {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} {t u : String} (hs : pos.Splits t u) :
    pos.find? p = none ↔ ∀ c ∈ u.toList, ¬ p c := by
  rw [Pos.find?_prop_eq_none_iff]
  constructor
  · intro h c hc
    obtain ⟨pos', hle, hne, hget⟩ := hs.mem_toList_right_iff.mp hc
    subst hget; exact h pos' hle hne
  · intro h pos' hle hne
    exact h _ (hs.mem_toList_right_iff.mpr ⟨pos', hle, hne, rfl⟩)

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

theorem Pos.find?_bool_eq_some_iff_splits {p : Char → Bool} {s : String} {pos : s.Pos}
    {t u : String} (hs : pos.Splits t u) {pos' : s.Pos} :
    pos.find? p = some pos' ↔
      ∃ v c w, pos'.Splits (t ++ v) (singleton c ++ w) ∧ p c ∧
        ∀ d ∈ v.toList, p d = false := by
  simp only [Pos.find?_eq_find?_toSlice, Option.map_eq_some_iff,
    Slice.Pos.find?_bool_eq_some_iff_splits (Pos.splits_toSlice_iff.mpr hs)]
  constructor
  · rintro ⟨q, ⟨v, c, w, hsplit, hpc, hmin⟩, rfl⟩
    exact ⟨v, c, w, Slice.Pos.splits_ofToSlice_iff.mpr hsplit, hpc, hmin⟩
  · rintro ⟨v, c, w, hsplit, hpc, hmin⟩
    exact ⟨pos'.toSlice, ⟨v, c, w, Pos.splits_toSlice_iff.mpr hsplit, hpc, hmin⟩, by simp⟩

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

theorem Pos.find?_bool_eq_none_iff_of_splits {p : Char → Bool} {s : String} {pos : s.Pos}
    {t u : String} (hs : pos.Splits t u) :
    pos.find? p = none ↔ ∀ c ∈ u.toList, p c = false := by
  rw [Pos.find?_eq_find?_toSlice, Option.map_eq_none_iff]
  exact Slice.Pos.find?_bool_eq_none_iff_of_splits (Pos.splits_toSlice_iff.mpr hs)

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

theorem Pos.find?_prop_eq_some_iff_splits {p : Char → Prop} [DecidablePred p] {s : String}
    {pos : s.Pos} {t u : String} (hs : pos.Splits t u) {pos' : s.Pos} :
    pos.find? p = some pos' ↔
      ∃ v c w, pos'.Splits (t ++ v) (singleton c ++ w) ∧ p c ∧ ∀ d ∈ v.toList, ¬ p d := by
  simp only [Pos.find?_eq_find?_toSlice, Option.map_eq_some_iff,
    Slice.Pos.find?_prop_eq_some_iff_splits (Pos.splits_toSlice_iff.mpr hs)]
  constructor
  · rintro ⟨q, ⟨v, c, w, hsplit, hpc, hmin⟩, rfl⟩
    exact ⟨v, c, w, Slice.Pos.splits_ofToSlice_iff.mpr hsplit, hpc, hmin⟩
  · rintro ⟨v, c, w, hsplit, hpc, hmin⟩
    exact ⟨pos'.toSlice, ⟨v, c, w, Pos.splits_toSlice_iff.mpr hsplit, hpc, hmin⟩, by simp⟩

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

theorem Pos.find?_prop_eq_none_iff_of_splits {p : Char → Prop} [DecidablePred p] {s : String}
    {pos : s.Pos} {t u : String} (hs : pos.Splits t u) :
    pos.find? p = none ↔ ∀ c ∈ u.toList, ¬ p c := by
  rw [Pos.find?_eq_find?_toSlice, Option.map_eq_none_iff]
  exact Slice.Pos.find?_prop_eq_none_iff_of_splits (Pos.splits_toSlice_iff.mpr hs)

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

theorem find?_bool_eq_some_iff_splits {p : Char → Bool} {s : String} {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ t c u, pos.Splits t (singleton c ++ u) ∧ p c ∧ ∀ d ∈ t.toList, p d = false := by
  simp only [find?_eq_find?_toSlice, Option.map_eq_some_iff,
    Slice.find?_bool_eq_some_iff_splits]
  constructor
  · rintro ⟨q, ⟨t, c, u, hsplit, hpc, hmin⟩, rfl⟩
    exact ⟨t, c, u, Slice.Pos.splits_ofToSlice_iff.mpr hsplit, hpc, hmin⟩
  · rintro ⟨t, c, u, hsplit, hpc, hmin⟩
    exact ⟨pos.toSlice, ⟨t, c, u, Pos.splits_toSlice_iff.mpr hsplit, hpc, hmin⟩, by simp⟩

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

theorem find?_prop_eq_some_iff_splits {p : Char → Prop} [DecidablePred p] {s : String}
    {pos : s.Pos} :
    s.find? p = some pos ↔
      ∃ t c u, pos.Splits t (singleton c ++ u) ∧ p c ∧ ∀ d ∈ t.toList, ¬ p d := by
  simp only [find?_eq_find?_toSlice, Option.map_eq_some_iff,
    Slice.find?_prop_eq_some_iff_splits]
  constructor
  · rintro ⟨q, ⟨t, c, u, hsplit, hpc, hmin⟩, rfl⟩
    exact ⟨t, c, u, Slice.Pos.splits_ofToSlice_iff.mpr hsplit, hpc, hmin⟩
  · rintro ⟨t, c, u, hsplit, hpc, hmin⟩
    exact ⟨pos.toSlice, ⟨t, c, u, Pos.splits_toSlice_iff.mpr hsplit, hpc, hmin⟩, by simp⟩

@[simp]
theorem contains_bool_eq {p : Char → Bool} {s : String} : s.contains p = s.toList.any p := by
  simp [contains_eq_contains_toSlice, Slice.contains_bool_eq, copy_toSlice]

@[simp]
theorem contains_prop_eq {p : Char → Prop} [DecidablePred p] {s : String} :
    s.contains p = s.toList.any p := by
  simp [contains_eq_contains_toSlice, Slice.contains_prop_eq, copy_toSlice]

end String
