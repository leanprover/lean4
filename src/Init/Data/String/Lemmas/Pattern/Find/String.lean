/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
import all Init.Data.String.Slice
import all Init.Data.String.Search
import all Init.Data.String.Pattern.String
import Init.Data.String.Lemmas.Pattern.Find.Basic
import Init.Data.String.Lemmas.Pattern.String.Basic
import Init.Data.String.Lemmas.Pattern.String.ForwardSearcher
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.String.Lemmas.Order
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Iterate
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Grind
import Init.Data.Option.Lemmas
import Init.Data.String.OrderInstances
import Init.Data.List.Sublist

namespace String.Slice

open Pattern.Model in
private theorem contains_eq_true_of_isEmpty {pat : Slice} (hpat : pat.isEmpty = true) (s : Slice) :
    s.contains pat = true := by
  rw [contains]
  rw [← Std.Iter.any_toList]
  simp only [Pattern.ToForwardSearcher.toSearcher]
  simp only [Pattern.ForwardSliceSearcher.iter,
    dif_pos (show pat.utf8ByteSize = 0 from by simpa [isEmpty_eq] using hpat)]
  obtain ⟨l, hl⟩ :=
    Pattern.Model.ForwardSliceSearcher.toList_iter_emptyBefore s s.startPos
  rw [hl]; simp [List.any_cons]

private theorem isInfix_toList_iff {t s : String} :
    t.toList <:+: s.toList ↔ ∃ s₁ s₂, s = s₁ ++ t ++ s₂ := by
  constructor
  · rintro ⟨l₁, l₂, h⟩
    exact ⟨.ofList l₁, .ofList l₂,
      String.toList_inj.mp (by simp [String.toList_append, h])⟩
  · rintro ⟨s₁, s₂, rfl⟩
    exact ⟨s₁.toList, s₂.toList, by simp [String.toList_append, List.append_assoc]⟩

@[simp]
theorem contains_string_eq {t s : Slice} :
    s.contains t ↔ t.copy.toList <:+: s.copy.toList := by
  by_cases ht : t.isEmpty
  · -- Empty pattern: always contained
    simp [eq_true (contains_eq_true_of_isEmpty ht s), copy_eq_empty_iff.mpr ht, String.toList_empty]
  · -- Non-empty pattern: use the pattern model
    simp only [Bool.not_eq_true] at ht
    have := Pattern.Model.ForwardSliceSearcher.lawfulToForwardSearcherModel ht
    constructor
    · intro h
      rw [Pattern.Model.contains_eq_true_iff] at h
      obtain ⟨pos, hm⟩ := h
      rw [Pattern.Model.ForwardSliceSearcher.matchesAt_iff_splits ht] at hm
      obtain ⟨t₁, t₂, hsplit⟩ := hm
      rw [isInfix_toList_iff]
      exact ⟨t₁, t₂, by rw [hsplit.eq_append, append_assoc]⟩
    · intro h
      rw [Pattern.Model.contains_eq_true_iff]
      rw [isInfix_toList_iff] at h
      obtain ⟨s₁, s₂, heq⟩ := h
      have hvalid : s₁.rawEndPos.IsValidForSlice s :=
        Pos.Raw.isValidForSlice_iff_exists_append.mpr
          ⟨s₁, t.copy ++ s₂, by rw [← append_assoc]; exact heq, rfl⟩
      exact ⟨s.pos _ hvalid,
        (Pattern.Model.ForwardSliceSearcher.matchesAt_iff_splits ht).mpr
          ⟨s₁, s₂, ⟨by rw [← append_assoc]; exact heq, by simp⟩⟩⟩

end Slice

@[simp]
theorem contains_string_eq {t s : String} :
    s.contains t ↔ t.toList <:+: s.toList := by
  rw [contains]
  -- Goal: s.toSlice.contains t ↔ t.toList <:+: s.toList
  by_cases ht : t = ""
  · subst ht
    constructor
    · intro _; exact List.nil_infix
    · intro _
      rw [Slice.contains]
      rw [← Std.Iter.any_toList]
      simp only [Slice.Pattern.ToForwardSearcher.toSearcher]
      simp only [Slice.Pattern.ForwardSliceSearcher.iter,
        dif_pos (show "".toSlice.utf8ByteSize = 0 from by simp)]
      obtain ⟨l, hl⟩ :=
        Slice.Pattern.Model.ForwardSliceSearcher.toList_iter_emptyBefore s.toSlice s.toSlice.startPos
      rw [hl]; simp [List.any_cons]
  · have := Slice.Pattern.Model.ForwardStringSearcher.lawfulToForwardSearcherModel (pat := t) ht
    constructor
    · intro h
      rw [Slice.Pattern.Model.contains_eq_true_iff] at h
      obtain ⟨pos, hm⟩ := h
      rw [Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_splits ht] at hm
      obtain ⟨t₁, t₂, hsplit⟩ := hm
      rw [Slice.isInfix_toList_iff]
      exact ⟨t₁, t₂, by rw [← copy_toSlice (s := s), hsplit.eq_append, append_assoc]⟩
    · intro h
      rw [Slice.Pattern.Model.contains_eq_true_iff]
      rw [Slice.isInfix_toList_iff] at h
      obtain ⟨s₁, s₂, heq⟩ := h
      have hvalid : s₁.rawEndPos.IsValidForSlice s.toSlice :=
        Pos.Raw.isValidForSlice_iff_exists_append.mpr
          ⟨s₁, t ++ s₂, by rw [copy_toSlice, ← append_assoc]; exact heq, rfl⟩
      exact ⟨s.toSlice.pos _ hvalid,
        (Slice.Pattern.Model.ForwardStringSearcher.matchesAt_iff_splits ht).mpr
          ⟨s₁, s₂, ⟨by rw [copy_toSlice, ← append_assoc]; exact heq, by simp⟩⟩⟩

end String
