/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Lemmas.Pattern.Basic
public import Init.Data.String.Pattern.String
import all Init.Data.String.Pattern.String
import Init.Data.String.Lemmas.Pattern.Memcmp
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.String.Lemmas.Basic
import Init.Omega
import Init.Data.ByteArray.Lemmas

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

theorem startsWith_iff {pat s : Slice} : startsWith pat s ↔ ∃ t, s.copy = pat.copy ++ t := by
  rw [startsWith]
  simp [Internal.memcmpSlice_eq_true_iff, utf8ByteSize_eq_size_toByteArray_copy, -size_toByteArray]
  generalize pat.copy = pat
  generalize s.copy = s
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩
  · suffices pat.rawEndPos.IsValid s by
      have h₁ : (s.sliceTo (s.pos _ this)).copy = pat := by
        simpa [← toByteArray_inj, copy_toByteArray_sliceTo]
      have := (s.pos _ this).splits
      rw [h₁] at this
      refine ⟨_, this.eq_append⟩
    rw [Pos.Raw.isValid_iff_isValidUTF8_extract_zero]
    refine ⟨by simpa using h₁, ?_⟩
    simp only [size_toByteArray] at h₂
    simpa [h₂] using pat.isValidUTF8
  · rintro ⟨t, rfl⟩
    simp [-size_toByteArray, ByteArray.extract_append]

theorem dropPrefix?_eq_some_iff {pat s : Slice} {pos : s.Pos} :
    dropPrefix? pat s = some pos ↔ (s.sliceTo pos).copy = pat.copy := by
  fun_cases dropPrefix? with
  | case1 h =>
    simp only [offset_startPos, Pos.Raw.offsetBy_zero, Option.some.injEq]
    obtain ⟨t, ht⟩ := startsWith_iff.1 h
    have hval : pat.rawEndPos.IsValidForSlice s := by
      rw [← Pos.Raw.isValid_copy_iff, ht, ← Slice.rawEndPos_copy]
      exact Pos.Raw.isValid_rawEndPos.append_right _
    have hsp : (s.pos _ hval).Splits pat.copy t := ⟨ht, by simp⟩
    rw [pos!_eq_pos hval]
    exact ⟨(· ▸ hsp.copy_sliceTo_eq), fun h => hsp.pos_eq (h ▸ pos.splits)⟩
  | case2 h =>
    simp only [startsWith_iff, not_exists] at h
    simp only [reduceCtorEq, false_iff]
    intro heq
    have := h (s.sliceFrom pos).copy
    simp [← heq, pos.splits.eq_append] at this

end ForwardSliceSearcher


end String.Slice.Pattern
