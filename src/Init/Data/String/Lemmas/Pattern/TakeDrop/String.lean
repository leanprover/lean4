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
  match h : pat.isEmpty with
  | false =>
    have := ForwardSliceSearcher.lawfulForwardPatternModel h
    rw [Pattern.Model.skipPrefix?_eq_some_iff, ForwardSliceSearcher.isLongestMatch_iff_splits h]
  | true => simp [skipPrefix?_slice_of_isEmpty h, (show pat.copy = "" by simpa), eq_comm]

theorem startsWith_slice_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    s.startsWith pat = true := by
  rw [startsWith_eq_forwardPatternStartsWith, ForwardSliceSearcher.startsWith_of_isEmpty hpat]

@[simp]
theorem startsWith_slice_iff {pat s : Slice} :
    s.startsWith pat ↔ pat.copy.toList <+: s.copy.toList := by
  match h : pat.isEmpty with
  | false =>
    have := ForwardSliceSearcher.lawfulForwardPatternModel h
    simp only [Model.startsWith_iff, ForwardSliceSearcher.matchesAt_iff_splits h,
      splits_startPos_iff, exists_and_left, exists_eq_left]
    simp only [← toList_inj, toList_append, List.prefix_iff_exists_append_eq]
    exact ⟨fun ⟨t, ht⟩ => ⟨t.toList, by simp [ht]⟩, fun ⟨t, ht⟩ => ⟨String.ofList t, by simp [← ht]⟩⟩
  | true => simp [startsWith_slice_of_isEmpty h, (show pat.copy = "" by simpa)]

@[simp]
theorem startsWith_slice_eq_false_iff {pat s : Slice} :
    s.startsWith pat = false ↔ ¬ (pat.copy.toList <+: s.copy.toList) := by
  simp [← Bool.not_eq_true, startsWith_slice_iff]

theorem dropPrefix?_slice_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    s.dropPrefix? pat = some s := by
  simp [dropPrefix?_eq_map_skipPrefix?, skipPrefix?_slice_of_isEmpty hpat]

theorem eq_append_of_dropPrefix?_slice_eq_some {pat s res : Slice} (h : s.dropPrefix? pat = some res) :
    s.copy = pat.copy ++ res.copy := by
  match hpat : pat.isEmpty with
  | false =>
    have := ForwardSliceSearcher.lawfulForwardPatternModel hpat
    have := Pattern.Model.eq_append_of_dropPrefix?_eq_some h
    simp only [ForwardPatternModel.Matches] at this
    obtain ⟨_, ⟨-, rfl⟩, h⟩ := this
    exact h
  | true => simp [Option.some.inj (h ▸ dropPrefix?_slice_of_isEmpty hpat), (show pat.copy = "" by simpa)]

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
  simp [startsWith_eq_startsWith_toSlice]

@[simp]
theorem startsWith_slice_eq_false_iff {pat : Slice} {s : String} :
    s.startsWith pat = false ↔ ¬ (pat.copy.toList <+: s.toList) := by
  simp [startsWith_eq_startsWith_toSlice]

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
  simp [startsWith_eq_startsWith_toSlice]

@[simp]
theorem startsWith_string_iff {pat s : String} :
    s.startsWith pat ↔ pat.toList <+: s.toList := by
  simp [startsWith_eq_startsWith_toSlice]

@[simp]
theorem startsWith_string_eq_false_iff {pat s : String} :
    s.startsWith pat = false ↔ ¬ (pat.toList <+: s.toList) := by
  simp [startsWith_eq_startsWith_toSlice]

@[simp]
theorem dropPrefix?_string_empty {s : String} : s.dropPrefix? "" = some s.toSlice := by
  simp [dropPrefix?_eq_dropPrefix?_toSlice]

theorem eq_append_of_dropPrefix?_string_eq_some {s pat : String} {res : Slice} (h : s.dropPrefix? pat = some res) :
    s = pat ++ res.copy := by
  rw [dropPrefix?_eq_dropPrefix?_toSlice] at h
  simpa using Slice.eq_append_of_dropPrefix?_string_eq_some h

end String
