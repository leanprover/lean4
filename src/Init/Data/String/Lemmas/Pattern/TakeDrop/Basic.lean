/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.TakeDrop
public import Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.String.Slice
import all Init.Data.String.TakeDrop

public section

open String.Slice Pattern Model

namespace String

namespace Slice

theorem skipPrefix?_eq_forwardPatternSkipPrefix? {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.skipPrefix? pat = ForwardPattern.skipPrefix? pat s := (rfl)

theorem startsWith_eq_forwardPatternStartsWith {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.startsWith pat = ForwardPattern.startsWith pat s := (rfl)

theorem dropPrefix?_eq_map_skipPrefix? {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : Slice} :
    s.dropPrefix? pat = (s.skipPrefix? pat).map s.sliceFrom := (rfl)

theorem Pattern.Model.skipPrefix?_eq_some_iff {ρ : Type} {pat : ρ} [ForwardPatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ IsLongestMatch pat pos := by
  rw [skipPrefix?_eq_forwardPatternSkipPrefix?, LawfulForwardPatternModel.skipPrefix?_eq_some_iff]

theorem Pattern.Model.skipPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.skipPrefix? pat = none ↔ ¬ MatchesAt pat s.startPos := by
  rw [skipPrefix?_eq_forwardPatternSkipPrefix?, LawfulForwardPatternModel.skipPrefix?_eq_none_iff]

@[simp]
theorem isSome_skipPrefix? {ρ : Type} {pat : ρ} [ForwardPattern pat] [LawfulForwardPattern pat] {s : Slice} :
    (s.skipPrefix? pat).isSome = s.startsWith pat := by
  rw [startsWith_eq_forwardPatternStartsWith, skipPrefix?, LawfulForwardPattern.startsWith_eq]

theorem Pattern.Model.startsWith_eq_false_iff {ρ : Type} {pat : ρ} [ForwardPatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.startsWith pat = false ↔ ¬ MatchesAt pat s.startPos := by
  rw [← Pattern.Model.skipPrefix?_eq_none_iff, ← Option.isNone_iff_eq_none,
    ← isSome_skipPrefix?, Option.isSome_eq_false_iff]

theorem Pattern.Model.startsWith_iff {ρ : Type} {pat : ρ} [ForwardPatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.startsWith pat = true ↔ MatchesAt pat s.startPos := by
  rw [← Bool.not_eq_false, startsWith_eq_false_iff, Classical.not_not]

@[simp]
theorem skipPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] [LawfulForwardPattern pat]
    {s : Slice} : s.skipPrefix? pat = none ↔ s.startsWith pat = false := by
  rw [← Option.isNone_iff_eq_none, ← Option.isSome_eq_false_iff, isSome_skipPrefix?]

@[simp]
theorem dropPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] [LawfulForwardPattern pat]
    {s : Slice} : s.dropPrefix? pat = none ↔ s.startsWith pat = false := by
  simp [dropPrefix?_eq_map_skipPrefix?]

theorem Pattern.Model.eq_append_of_dropPrefix?_eq_some {ρ : Type} {pat : ρ} [ForwardPatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s res : Slice} (h : s.dropPrefix? pat = some res) :
    ∃ t, ForwardPatternModel.Matches pat t ∧ s.copy = t ++ res.copy := by
  simp only [dropPrefix?_eq_map_skipPrefix?, Option.map_eq_some_iff, skipPrefix?_eq_some_iff] at h
  obtain ⟨pos, h₁, h₂⟩ := h
  exact ⟨(s.sliceTo pos).copy, h₁.isMatch.matches_copy, by simp [← h₂, ← copy_eq_copy_sliceTo]⟩

end Slice

theorem skipPrefix?_eq_skipPrefix?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.skipPrefix? pat = (s.toSlice.skipPrefix? pat).map Pos.ofToSlice := (rfl)

theorem startsWith_eq_startsWith_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.startsWith pat = s.toSlice.startsWith pat := (rfl)

theorem dropPrefix?_eq_dropPrefix?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.dropPrefix? pat = s.toSlice.dropPrefix? pat := (rfl)

end String
