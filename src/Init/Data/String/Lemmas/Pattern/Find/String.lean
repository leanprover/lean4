/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.String
import Init.ByCases
import Init.Data.String.Lemmas.Pattern.Find.Basic
import Init.Data.String.Lemmas.Pattern.String.ForwardSearcher
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.List.Sublist

public section

namespace String.Slice

open Pattern.Model in
private theorem contains_eq_true_of_isEmpty {pat : Slice} (hpat : pat.isEmpty = true) (s : Slice) :
    s.contains pat = true := by
  rw [contains, ← Std.Iter.any_toList, ForwardSliceSearcher.toSearcher_of_isEmpty hpat,
    ForwardSliceSearcher.toList_emptyBefore_eq]
  split <;> simp [List.any_cons]

open Pattern.Model in
private theorem contains_string_eq_true_of_empty {pat : String} (hpat : pat = "") (s : Slice) :
    s.contains pat = true := by
  subst hpat
  rw [contains, ← Std.Iter.any_toList, ForwardStringSearcher.toSearcher_empty,
    ForwardSliceSearcher.toList_emptyBefore_eq]
  split <;> simp [List.any_cons]

private theorem isInfix_toList_iff {t s : String} :
    t.toList <:+: s.toList ↔ ∃ s₁ s₂, s = s₁ ++ t ++ s₂ := by
  constructor
  · rintro ⟨l₁, l₂, h⟩
    exact ⟨.ofList l₁, .ofList l₂,
      String.toList_inj.mp (by simp [String.toList_append, h])⟩
  · rintro ⟨s₁, s₂, rfl⟩
    exact ⟨s₁.toList, s₂.toList, by simp [String.toList_append, List.append_assoc]⟩

@[simp]
theorem contains_slice_iff {t s : Slice} :
    s.contains t ↔ t.copy.toList <:+: s.copy.toList := by
  by_cases ht : t.isEmpty
  · simp [contains_eq_true_of_isEmpty ht s, copy_eq_empty_iff.mpr ht, String.toList_empty]
  · simp only [Bool.not_eq_true] at ht
    have := Pattern.Model.ForwardSliceSearcher.strictPatternModel ht
    have := Pattern.Model.ForwardSliceSearcher.lawfulToForwardSearcherModel ht
    simp only [Pattern.Model.contains_eq_true_iff,
      Pattern.Model.ForwardSliceSearcher.exists_matchesAt_iff_eq_append, isInfix_toList_iff]

@[simp]
theorem contains_string_iff {t : String} {s : Slice} :
    s.contains t ↔ t.toList <:+: s.copy.toList := by
  simp [contains_string_eq_contains_toSlice, contains_slice_iff, copy_toSlice]

@[simp]
theorem contains_slice_eq_false_iff {t s : Slice} :
    s.contains t = false ↔ ¬(t.copy.toList <:+: s.copy.toList) :=
  Bool.eq_false_iff.trans (not_congr contains_slice_iff)

@[simp]
theorem contains_string_eq_false_iff {t : String} {s : Slice} :
    s.contains t = false ↔ ¬(t.toList <:+: s.copy.toList) :=
  Bool.eq_false_iff.trans (not_congr contains_string_iff)

end Slice

@[simp]
theorem contains_slice_iff {t : Slice} {s : String} :
    s.contains t ↔ t.copy.toList <:+: s.toList := by
  simp [contains_eq_contains_toSlice, Slice.contains_slice_iff, copy_toSlice]

@[simp]
theorem contains_string_iff {t s : String} :
    s.contains t ↔ t.toList <:+: s.toList := by
  simp [contains_eq_contains_toSlice, Slice.contains_string_iff, copy_toSlice]

@[simp]
theorem contains_slice_eq_false_iff {t : Slice} {s : String} :
    s.contains t = false ↔ ¬(t.copy.toList <:+: s.toList) :=
  Bool.eq_false_iff.trans (not_congr contains_slice_iff)

@[simp]
theorem contains_string_eq_false_iff {t s : String} :
    s.contains t = false ↔ ¬(t.toList <:+: s.toList) :=
  Bool.eq_false_iff.trans (not_congr contains_string_iff)

/-
  Used internally by the `cbv` tactic.
-/
@[cbv_eval]
theorem contains_string_eq_internal {t s : String} :
    s.contains t = t.toList.isInfixOf_internal s.toList := by
  rw [Bool.eq_iff_iff, contains_string_iff, List.isInfixOf_internal_iff_isInfix]

end String
