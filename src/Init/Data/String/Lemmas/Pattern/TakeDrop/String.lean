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

public section

open String.Slice Pattern Model

namespace String

namespace Slice

@[simp]
theorem skipPrefix?_slice_eq_some_iff {pat s : Slice} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ ∃ t, pos.Splits pat.copy t := by
  match h : pat.isEmpty with
  | false =>
    have := ForwardSliceSearcher.lawfulForwardPatternModel h
    rw [Pattern.Model.skipPrefix?_eq_some_iff, ForwardSliceSearcher.isLongestMatch_iff_splits h]
  | true =>
    rw [skipPrefix?_eq_forwardPatternSkipPrefix?, ForwardSliceSearcher.skipPrefix?_of_isEmpty h]
    simp [(show pat.copy = "" by simpa), eq_comm]

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
  | true =>
    rw [startsWith_eq_forwardPatternStartsWith, ForwardSliceSearcher.startsWith_of_isEmpty h]
    simp [(show pat.copy = "" by simpa)]

@[simp]
theorem startsWith_slice_eq_false_iff {pat s : Slice} :
    s.startsWith pat = false ↔ ¬ (pat.copy.toList <+: s.copy.toList) := by
  simp [← Bool.not_eq_true, startsWith_slice_iff]

@[simp]
theorem skipPrefix?_string_eq_some_iff {pat : String} {s : Slice} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ ∃ t, pos.Splits pat t := by
  simp [skipPrefix?_string_eq_skipPrefix?_toSlice]

@[simp]
theorem startsWith_string_iff {pat : String} {s : Slice} :
    s.startsWith pat ↔ pat.toList <+: s.copy.toList := by
  simp [startsWith_string_eq_startsWith_toSlice]

@[simp]
theorem startsWith_string_eq_false_iff {pat : String} {s : Slice} :
    s.startsWith pat = false ↔ ¬ (pat.toList <+: s.copy.toList) := by
  simp [startsWith_string_eq_startsWith_toSlice]

end Slice

@[simp]
theorem skipPrefix?_slice_eq_some_iff {pat : Slice} {s : String} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ ∃ t, pos.Splits pat.copy t := by
  simp only [skipPrefix?_eq_skipPrefix?_toSlice, Option.map_eq_some_iff,
    Slice.skipPrefix?_slice_eq_some_iff]
  refine ⟨?_, fun h => ⟨pos.toSlice, by simpa⟩⟩
  rintro ⟨pos, h, rfl⟩
  simpa

@[simp]
theorem startsWith_slice_iff {pat : Slice} {s : String} :
    s.startsWith pat ↔ pat.copy.toList <+: s.toList := by
  simp [startsWith_eq_startsWith_toSlice]

@[simp]
theorem startsWith_slice_eq_false_iff {pat : Slice} {s : String} :
    s.startsWith pat = false ↔ ¬ (pat.copy.toList <+: s.toList) := by
  simp [startsWith_eq_startsWith_toSlice]

@[simp]
theorem skipPrefix?_string_eq_some_iff {pat s : String} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ ∃ t, pos.Splits pat t := by
  simp only [skipPrefix?_eq_skipPrefix?_toSlice, Option.map_eq_some_iff,
    Slice.skipPrefix?_string_eq_some_iff]
  refine ⟨?_, fun h => ⟨pos.toSlice, by simpa⟩⟩
  rintro ⟨pos, h, rfl⟩
  simpa

@[simp]
theorem startsWith_string_iff {pat s : String} :
    s.startsWith pat ↔ pat.toList <+: s.toList := by
  simp [startsWith_eq_startsWith_toSlice]

@[simp]
theorem startsWith_string_eq_false_iff {pat s : String} :
    s.startsWith pat = false ↔ ¬ (pat.toList <+: s.toList) := by
  simp [startsWith_eq_startsWith_toSlice]

end String
