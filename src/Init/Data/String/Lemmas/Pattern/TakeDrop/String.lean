/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.TakeDrop
public import Init.Data.String.Lemmas.Splits
import Init.Data.String.Lemmas.Pattern.TakeDrop.Basic
import Init.Data.String.Lemmas.Pattern.String
import Init.Data.List.Sublist
import Init.Data.Option.Lemmas
import Init.Data.String.Lemmas.Basic

public section

open String.Slice Pattern Model

namespace String

namespace Slice

theorem skipPrefix?_slice_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    s.skipPrefix? pat = some s.startPos := by
  rw [skipPrefix?_eq_forwardPatternSkipPrefix?, ForwardSliceSearcher.skipPrefix?_of_isEmpty hpat]

@[simp]
theorem skipPrefix?_slice_eq_some_iff {pat s : Slice} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ ∃ t, pos.Splits pat.copy t := by
  rw [Pattern.Model.skipPrefix?_eq_some_iff, ForwardSliceSearcher.isLongestMatch_iff_splits]

theorem startsWith_slice_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    s.startsWith pat = true := by
  rw [startsWith_eq_forwardPatternStartsWith, ForwardSliceSearcher.startsWith_of_isEmpty hpat]

@[simp]
theorem startsWith_slice_iff {pat s : Slice} :
    s.startsWith pat ↔ pat.copy.toList <+: s.copy.toList := by
  simp only [Model.startsWith_iff, ForwardSliceSearcher.matchesAt_iff_splits,
    splits_startPos_iff, exists_and_left, exists_eq_left]
  simp only [← toList_inj, toList_append, List.prefix_iff_exists_append_eq]
  exact ⟨fun ⟨t, ht⟩ => ⟨t.toList, by simp [ht]⟩, fun ⟨t, ht⟩ => ⟨String.ofList t, by simp [← ht]⟩⟩

@[simp]
theorem startsWith_slice_eq_false_iff {pat s : Slice} :
    s.startsWith pat = false ↔ ¬ (pat.copy.toList <+: s.copy.toList) := by
  simp [← Bool.not_eq_true, startsWith_slice_iff]

theorem dropPrefix?_slice_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    s.dropPrefix? pat = some s := by
  simp [dropPrefix?_eq_map_skipPrefix?, skipPrefix?_slice_of_isEmpty hpat]

theorem eq_append_of_dropPrefix?_slice_eq_some {pat s res : Slice} (h : s.dropPrefix? pat = some res) :
    s.copy = pat.copy ++ res.copy := by
  have := Pattern.Model.eq_append_of_dropPrefix?_eq_some h
  simp only [PatternModel.Matches] at this
  obtain ⟨_, ⟨-, rfl⟩, h⟩ := this
  exact h

@[simp]
theorem all_slice_iff {pat s : Slice} : s.all pat ↔ ∃ n, s.copy = String.join (List.replicate n pat.copy) := by
  simp [Pattern.Model.all_eq_true_iff, ForwardSliceSearcher.isLongestMatchAtChain_startPos_endPos_iff]

@[simp]
theorem revAll_slice_iff {pat s : Slice} : s.revAll pat ↔ ∃ n, s.copy = String.join (List.replicate n pat.copy) := by
  simp [Pattern.Model.revAll_eq_true_iff, ForwardSliceSearcher.isLongestRevMatchAtChain_startPos_endPos_iff]

@[simp]
theorem skipPrefix?_string_eq_some_iff {pat : String} {s : Slice} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ ∃ t, pos.Splits pat t := by
  simp [skipPrefix?_string_eq_skipPrefix?_toSlice]

@[simp]
theorem skipPrefix?_string_empty {s : Slice} : s.skipPrefix? "" = some s.startPos := by
  simp

@[simp]
theorem startsWith_string_iff {pat : String} {s : Slice} :
    s.startsWith pat ↔ pat.toList <+: s.copy.toList := by
  simp [startsWith_string_eq_startsWith_toSlice]

@[simp]
theorem startsWith_string_empty {s : Slice} : s.startsWith "" = true := by
  simp

@[simp]
theorem startsWith_string_eq_false_iff {pat : String} {s : Slice} :
    s.startsWith pat = false ↔ ¬ (pat.toList <+: s.copy.toList) := by
  simp [startsWith_string_eq_startsWith_toSlice]

@[simp]
theorem dropPrefix?_string_empty {s : Slice} : s.dropPrefix? "" = some s := by
  simpa [dropPrefix?_string_eq_dropPrefix?_toSlice] using dropPrefix?_slice_of_isEmpty (by simp)

theorem eq_append_of_dropPrefix?_string_eq_some {pat : String} {s res : Slice} (h : s.dropPrefix? pat = some res) :
    s.copy = pat ++ res.copy := by
  rw [dropPrefix?_string_eq_dropPrefix?_toSlice] at h
  simpa using eq_append_of_dropPrefix?_slice_eq_some h


theorem skipSuffix?_slice_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    s.skipSuffix? pat = some s.endPos := by
  rw [skipSuffix?_eq_backwardPatternSkipSuffix?, BackwardSliceSearcher.skipSuffix?_of_isEmpty hpat]

@[simp]
theorem skipSuffix?_slice_eq_some_iff {pat s : Slice} {pos : s.Pos} :
    s.skipSuffix? pat = some pos ↔ ∃ t, pos.Splits t pat.copy := by
  rw [Pattern.Model.skipSuffix?_eq_some_iff, ForwardSliceSearcher.isLongestRevMatch_iff_splits]

theorem endsWith_slice_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    s.endsWith pat = true := by
  rw [endsWith_eq_backwardPatternEndsWith, BackwardSliceSearcher.endsWith_of_isEmpty hpat]

@[simp]
theorem endsWith_slice_iff {pat s : Slice} :
    s.endsWith pat ↔ pat.copy.toList <:+ s.copy.toList := by
  simp only [Model.endsWith_iff, ForwardSliceSearcher.revMatchesAt_iff_splits,
    splits_endPos_iff, exists_eq_right]
  simp only [← toList_inj, toList_append, List.suffix_iff_exists_append_eq]
  exact ⟨fun ⟨t, ht⟩ => ⟨t.toList, by simp [ht]⟩, fun ⟨t, ht⟩ => ⟨String.ofList t, by simp [← ht]⟩⟩

@[simp]
theorem endsWith_slice_eq_false_iff {pat s : Slice} :
    s.endsWith pat = false ↔ ¬ (pat.copy.toList <:+ s.copy.toList) := by
  simp [← Bool.not_eq_true, endsWith_slice_iff]

theorem dropSuffix?_slice_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    s.dropSuffix? pat = some s := by
  simp [dropSuffix?_eq_map_skipSuffix?, skipSuffix?_slice_of_isEmpty hpat]

theorem eq_append_of_dropSuffix?_slice_eq_some {pat s res : Slice} (h : s.dropSuffix? pat = some res) :
    s.copy = res.copy ++ pat.copy := by
  have := Pattern.Model.eq_append_of_dropSuffix?_eq_some h
  simp only [PatternModel.Matches] at this
  obtain ⟨_, ⟨-, rfl⟩, h⟩ := this
  exact h

@[simp]
theorem skipSuffix?_string_eq_some_iff' {pat : String} {s : Slice} {pos : s.Pos} :
    s.skipSuffix? pat = some pos ↔ ∃ t, pos.Splits t pat := by
  simp [skipSuffix?_string_eq_skipSuffix?_toSlice]

@[simp]
theorem skipSuffix?_string_empty {s : Slice} : s.skipSuffix? "" = some s.endPos := by
  simp

@[simp]
theorem endsWith_string_iff {pat : String} {s : Slice} :
    s.endsWith pat ↔ pat.toList <:+ s.copy.toList := by
  simp [endsWith_string_eq_endsWith_toSlice]

@[simp]
theorem endsWith_string_empty {s : Slice} : s.endsWith "" = true := by
  simp

@[simp]
theorem endsWith_string_eq_false_iff {pat : String} {s : Slice} :
    s.endsWith pat = false ↔ ¬ (pat.toList <:+ s.copy.toList) := by
  simp [endsWith_string_eq_endsWith_toSlice]

@[simp]
theorem dropSuffix?_string_empty {s : Slice} : s.dropSuffix? "" = some s := by
  simpa [dropSuffix?_string_eq_dropSuffix?_toSlice] using dropSuffix?_slice_of_isEmpty (by simp)

theorem eq_append_of_dropSuffix?_string_eq_some {pat : String} {s res : Slice} (h : s.dropSuffix? pat = some res) :
    s.copy = res.copy ++ pat := by
  rw [dropSuffix?_string_eq_dropSuffix?_toSlice] at h
  simpa using eq_append_of_dropSuffix?_slice_eq_some h

end Slice

theorem skipPrefix?_slice_of_isEmpty {pat : Slice} {s : String} (hpat : pat.isEmpty = true) :
    s.skipPrefix? pat = some s.startPos := by
  rw [skipPrefix?_eq_skipPrefix?_toSlice, Slice.skipPrefix?_slice_of_isEmpty hpat]
  simp

@[simp]
theorem skipPrefix?_slice_eq_some_iff {pat : Slice} {s : String} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ ∃ t, pos.Splits pat.copy t := by
  simp only [skipPrefix?_eq_skipPrefix?_toSlice, Option.map_eq_some_iff,
    Slice.skipPrefix?_slice_eq_some_iff]
  refine ⟨?_, fun h => ⟨pos.toSlice, by simpa⟩⟩
  rintro ⟨pos, h, rfl⟩
  simpa

theorem startsWith_slice_of_isEmpty {pat : Slice} {s : String} (hpat : pat.isEmpty = true) :
    s.startsWith pat = true := by
  rw [startsWith_eq_startsWith_toSlice, Slice.startsWith_slice_of_isEmpty hpat]

@[simp]
theorem startsWith_slice_iff {pat : Slice} {s : String} :
    s.startsWith pat ↔ pat.copy.toList <+: s.toList := by
  simp [← startsWith_toSlice]

@[simp]
theorem startsWith_slice_eq_false_iff {pat : Slice} {s : String} :
    s.startsWith pat = false ↔ ¬ (pat.copy.toList <+: s.toList) := by
  simp [← startsWith_toSlice]

theorem dropPrefix?_slice_of_isEmpty {pat : Slice} {s : String} (hpat : pat.isEmpty = true) :
    s.dropPrefix? pat = some s.toSlice := by
  rw [dropPrefix?_eq_dropPrefix?_toSlice, Slice.dropPrefix?_slice_of_isEmpty hpat]

theorem eq_append_of_dropPrefix?_slice_eq_some {pat res : Slice} {s : String} (h : s.dropPrefix? pat = some res) :
    s = pat.copy ++ res.copy := by
  rw [dropPrefix?_eq_dropPrefix?_toSlice] at h
  simpa using Slice.eq_append_of_dropPrefix?_slice_eq_some h

@[simp]
theorem skipPrefix?_string_empty {s : String} : s.skipPrefix? "" = some s.startPos := by
  simp [skipPrefix?_eq_skipPrefix?_toSlice]

@[simp]
theorem skipPrefix?_string_eq_some_iff {pat s : String} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ ∃ t, pos.Splits pat t := by
  simp only [skipPrefix?_eq_skipPrefix?_toSlice, Option.map_eq_some_iff,
    Slice.skipPrefix?_string_eq_some_iff]
  refine ⟨?_, fun h => ⟨pos.toSlice, by simpa⟩⟩
  rintro ⟨pos, h, rfl⟩
  simpa

@[simp]
theorem startsWith_string_empty {s : String} : s.startsWith "" = true := by
  simp [← startsWith_toSlice]

@[simp]
theorem startsWith_string_iff {pat s : String} :
    s.startsWith pat ↔ pat.toList <+: s.toList := by
  simp [← startsWith_toSlice]

@[simp]
theorem startsWith_string_eq_false_iff {pat s : String} :
    s.startsWith pat = false ↔ ¬ (pat.toList <+: s.toList) := by
  simp [← startsWith_toSlice]

@[simp]
theorem dropPrefix?_string_empty {s : String} : s.dropPrefix? "" = some s.toSlice := by
  simp [← dropPrefix?_toSlice]

theorem eq_append_of_dropPrefix?_string_eq_some {s pat : String} {res : Slice} (h : s.dropPrefix? pat = some res) :
    s = pat ++ res.copy := by
  rw [dropPrefix?_eq_dropPrefix?_toSlice] at h
  simpa using Slice.eq_append_of_dropPrefix?_string_eq_some h

end String
