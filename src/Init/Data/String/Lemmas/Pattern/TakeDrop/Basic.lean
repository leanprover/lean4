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

theorem Pattern.Model.skipPrefix?_eq_some_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    s.skipPrefix? pat = some pos ↔ IsLongestMatch pat pos := by
  rw [skipPrefix?_eq_forwardPatternSkipPrefix?, LawfulForwardPatternModel.skipPrefix?_eq_some_iff]

theorem Pattern.Model.skipPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.skipPrefix? pat = none ↔ ¬ MatchesAt pat s.startPos := by
  rw [skipPrefix?_eq_forwardPatternSkipPrefix?, LawfulForwardPatternModel.skipPrefix?_eq_none_iff]

@[simp]
theorem isSome_skipPrefix? {ρ : Type} {pat : ρ} [ForwardPattern pat] [LawfulForwardPattern pat] {s : Slice} :
    (s.skipPrefix? pat).isSome = s.startsWith pat := by
  rw [startsWith_eq_forwardPatternStartsWith, skipPrefix?, LawfulForwardPattern.startsWith_eq]

theorem Pattern.Model.startsWith_eq_false_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    s.startsWith pat = false ↔ ¬ MatchesAt pat s.startPos := by
  rw [← Pattern.Model.skipPrefix?_eq_none_iff, ← Option.isNone_iff_eq_none,
    ← isSome_skipPrefix?, Option.isSome_eq_false_iff]

theorem Pattern.Model.startsWith_iff {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
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

theorem Pattern.Model.eq_append_of_dropPrefix?_eq_some {ρ : Type} {pat : ρ} [PatternModel pat] [ForwardPattern pat]
    [LawfulForwardPatternModel pat] {s res : Slice} (h : s.dropPrefix? pat = some res) :
    ∃ t, PatternModel.Matches pat t ∧ s.copy = t ++ res.copy := by
  simp only [dropPrefix?_eq_map_skipPrefix?, Option.map_eq_some_iff, skipPrefix?_eq_some_iff] at h
  obtain ⟨pos, h₁, h₂⟩ := h
  exact ⟨(s.sliceTo pos).copy, h₁.isMatch.matches_copy, by simp [← h₂, ← copy_eq_copy_sliceTo]⟩

theorem skipSuffix?_eq_backwardPatternSkipSuffix? {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.skipSuffix? pat = BackwardPattern.skipSuffix? pat s := (rfl)

theorem endsWith_eq_backwardPatternEndsWith {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.endsWith pat = BackwardPattern.endsWith pat s := (rfl)

theorem dropSuffix?_eq_map_skipSuffix? {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : Slice} :
    s.dropSuffix? pat = (s.skipSuffix? pat).map s.sliceTo := (rfl)

theorem Pattern.Model.skipSuffix?_eq_some_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    s.skipSuffix? pat = some pos ↔ IsLongestRevMatch pat pos := by
  rw [skipSuffix?_eq_backwardPatternSkipSuffix?, LawfulBackwardPatternModel.skipSuffix?_eq_some_iff]

theorem Pattern.Model.skipSuffix?_eq_none_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    s.skipSuffix? pat = none ↔ ¬ RevMatchesAt pat s.endPos := by
  rw [skipSuffix?_eq_backwardPatternSkipSuffix?, LawfulBackwardPatternModel.skipSuffix?_eq_none_iff]

@[simp]
theorem isSome_skipSuffix? {ρ : Type} {pat : ρ} [BackwardPattern pat] [LawfulBackwardPattern pat] {s : Slice} :
    (s.skipSuffix? pat).isSome = s.endsWith pat := by
  rw [endsWith_eq_backwardPatternEndsWith, skipSuffix?, LawfulBackwardPattern.endsWith_eq]

theorem Pattern.Model.endsWith_eq_false_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    s.endsWith pat = false ↔ ¬ RevMatchesAt pat s.endPos := by
  rw [← Pattern.Model.skipSuffix?_eq_none_iff, ← Option.isNone_iff_eq_none,
    ← isSome_skipSuffix?, Option.isSome_eq_false_iff]

theorem Pattern.Model.endsWith_iff {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    s.endsWith pat = true ↔ RevMatchesAt pat s.endPos := by
  rw [← Bool.not_eq_false, endsWith_eq_false_iff, Classical.not_not]

@[simp]
theorem skipSuffix?_eq_none_iff {ρ : Type} {pat : ρ} [BackwardPattern pat] [LawfulBackwardPattern pat]
    {s : Slice} : s.skipSuffix? pat = none ↔ s.endsWith pat = false := by
  rw [← Option.isNone_iff_eq_none, ← Option.isSome_eq_false_iff, isSome_skipSuffix?]

@[simp]
theorem dropSuffix?_eq_none_iff {ρ : Type} {pat : ρ} [BackwardPattern pat] [LawfulBackwardPattern pat]
    {s : Slice} : s.dropSuffix? pat = none ↔ s.endsWith pat = false := by
  simp [dropSuffix?_eq_map_skipSuffix?]

theorem Pattern.Model.eq_append_of_dropSuffix?_eq_some {ρ : Type} {pat : ρ} [PatternModel pat] [BackwardPattern pat]
    [LawfulBackwardPatternModel pat] {s res : Slice} (h : s.dropSuffix? pat = some res) :
    ∃ t, PatternModel.Matches pat t ∧ s.copy = res.copy ++ t := by
  simp only [dropSuffix?_eq_map_skipSuffix?, Option.map_eq_some_iff, skipSuffix?_eq_some_iff] at h
  obtain ⟨pos, h₁, h₂⟩ := h
  exact ⟨(s.sliceFrom pos).copy, h₁.isRevMatch.matches_copy, by simp [← h₂, ← copy_eq_copy_sliceTo]⟩

end Slice

theorem skipPrefix?_eq_skipPrefix?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.skipPrefix? pat = (s.toSlice.skipPrefix? pat).map Pos.ofToSlice := (rfl)

theorem startsWith_eq_startsWith_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.startsWith pat = s.toSlice.startsWith pat := (rfl)

theorem dropPrefix?_eq_dropPrefix?_toSlice {ρ : Type} {pat : ρ} [ForwardPattern pat] {s : String} :
    s.dropPrefix? pat = s.toSlice.dropPrefix? pat := (rfl)

theorem skipSuffix?_eq_skipSuffix?_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.skipSuffix? pat = (s.toSlice.skipSuffix? pat).map Pos.ofToSlice := (rfl)

theorem endsWith_eq_endsWith_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.endsWith pat = s.toSlice.endsWith pat := (rfl)

theorem dropSuffix?_eq_dropSuffix?_toSlice {ρ : Type} {pat : ρ} [BackwardPattern pat] {s : String} :
    s.dropSuffix? pat = s.toSlice.dropSuffix? pat := (rfl)

end String
