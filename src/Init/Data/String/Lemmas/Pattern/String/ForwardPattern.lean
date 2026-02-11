/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Lemmas.Pattern.String.Basic
public import Init.Data.String.Pattern.String
import all Init.Data.String.Pattern.String
import Init.Data.String.Lemmas.Pattern.Memcmp
import Init.Data.String.Lemmas.Basic
import Init.Data.ByteArray.Lemmas

namespace String.Slice.Pattern

namespace ForwardSliceSearcher

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

theorem isSome_dropPrefix? {pat s : Slice} : (dropPrefix? pat s).isSome = startsWith pat s := by
  fun_cases dropPrefix? <;> simp_all

end ForwardSliceSearcher

namespace Model.ForwardSliceSearcher

open Pattern.ForwardSliceSearcher

public theorem lawfulForwardPatternModel {pat : Slice} (hpat : pat.isEmpty = false) :
    LawfulForwardPatternModel pat where
  dropPrefixOfNonempty?_eq h := rfl
  startsWith_eq s := isSome_dropPrefix?.symm
  dropPrefix?_eq_some_iff pos := by
    simp [ForwardPattern.dropPrefix?, dropPrefix?_eq_some_iff, isLongestMatch_iff hpat]

end Model.ForwardSliceSearcher

end String.Slice.Pattern
