/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Lemmas.Pattern.Basic
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.String.Lemmas.Basic
import Init.Data.ByteArray.Lemmas
import Init.Omega

public section

namespace String.Slice.Pattern

namespace ForwardSliceSearcher

instance {pat : Slice} : ForwardPatternModel pat where
  /-
  See the docstring of `ForwardPatternModel` for an explanation about why we disallow matching the
  empty string.

  Requiring `s ≠ ""` is a trick that allows us to give a `ForwardPatternModel` instance
  unconditionally, without forcing `pat.copy` to be non-empty (which would make it very awkward
  to state theorems about the instance). It does not change anything about the fact that all lemmas
  about this instance require `pat.isEmpty = false`.
  -/
  Matches s := s ≠ "" ∧ s = pat.copy
  not_matches_empty := by simp

instance {pat : Slice} : NoPrefixForwardPatternModel pat :=
  .of_length_eq (by simp +contextual [ForwardPatternModel.Matches])

theorem isMatch_iff {pat s : Slice} {pos : s.Pos} (h : pat.isEmpty = false) :
    IsMatch pat pos ↔ (s.sliceTo pos).copy = pat.copy := by
  simp only [Pattern.isMatch_iff, ForwardPatternModel.Matches, ne_eq, copy_eq_empty_iff,
    Bool.not_eq_true, and_iff_right_iff_imp]
  intro h'
  rw [← isEmpty_copy (s := s.sliceTo pos), h', isEmpty_copy, h]

theorem isLongestMatch_iff {pat s : Slice} {pos : s.Pos} (h : pat.isEmpty = false) :
    IsLongestMatch pat pos ↔ (s.sliceTo pos).copy = pat.copy := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff h]

theorem isLongestMatchAt_iff {pat s : Slice} {pos₁ pos₂ : s.Pos} (h : pat.isEmpty = false) :
    IsLongestMatchAt pat pos₁ pos₂ ↔ ∃ h, (s.slice pos₁ pos₂ h).copy = pat.copy := by
  simp [Pattern.isLongestMatchAt_iff, isLongestMatch_iff h]

theorem isLongestMatchAt_iff_splits {pat s : Slice} {pos₁ pos₂ : s.Pos} (h : pat.isEmpty = false) :
    IsLongestMatchAt pat pos₁ pos₂ ↔ ∃ t₁ t₂, pos₁.Splits t₁ (pat.copy ++ t₂) ∧
      pos₂.Splits (t₁ ++ pat.copy) t₂ := by
  simp only [isLongestMatchAt_iff h, copy_slice_eq_iff_splits]

theorem isLongestMatchAt_iff_extract {pat s : Slice} {pos₁ pos₂ : s.Pos} (h : pat.isEmpty = false) :
    IsLongestMatchAt pat pos₁ pos₂ ↔
      s.copy.toByteArray.extract pos₁.offset.byteIdx pos₂.offset.byteIdx = pat.copy.toByteArray := by
  rw [isLongestMatchAt_iff h]
  refine ⟨fun ⟨h, h'⟩ => ?_, fun h' => ?_⟩
  · simp [← h', toByteArray_copy_slice]
  · rw [← Slice.toByteArray_copy_ne_empty_iff, ← h', ne_eq, ByteArray.extract_eq_empty_iff] at h
    exact ⟨by simp [Pos.le_iff, Pos.Raw.le_iff]; omega,
      by simp [← h', ← toByteArray_inj, toByteArray_copy_slice]⟩

theorem matchesAt_iff_splits {pat s : Slice} {pos : s.Pos} (h : pat.isEmpty = false) :
    MatchesAt pat pos ↔ ∃ t₁ t₂, pos.Splits t₁ (pat.copy ++ t₂) := by
  simp only [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_splits h]
  exact ⟨fun ⟨e, t₁, t₂, ht₁, ht₂⟩ => ⟨t₁, t₂, ht₁⟩,
    fun ⟨t₁, t₂, ht⟩ => ⟨ht.rotateRight, t₁, t₂, ht, ht.splits_rotateRight⟩⟩

end ForwardSliceSearcher

end String.Slice.Pattern
