/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Lemmas.Pattern.String.Basic
public import Init.Data.String.Pattern.String
public import Init.Data.String.Slice
import all Init.Data.String.Pattern.String
import all Init.Data.String.Slice
import Init.Data.String.Lemmas.Pattern.Pred
import Init.Data.String.Lemmas.Pattern.Memcmp
import Init.Data.String.Lemmas.Basic
import Init.Data.ByteArray.Lemmas

namespace String.Slice.Pattern

namespace ForwardSliceSearcher

private theorem memcmpSlice_pat_eq_copy_toByteArray {pat : Slice} :
    pat.str.toByteArray.extract pat.startInclusive.offset.byteIdx
      (pat.startInclusive.offset.byteIdx + pat.rawEndPos.byteIdx) = pat.copy.toByteArray := by
  have := Pos.Raw.le_iff.1 pat.startInclusive_le_endExclusive
  rw [Slice.toByteArray_copy]
  congr 1
  simp [byteIdx_rawEndPos, utf8ByteSize_eq]; omega

private theorem memcmpSlice_s_eq_copy_extract {s : Slice} {n : Nat} (h : n ≤ s.utf8ByteSize) :
    s.str.toByteArray.extract s.startInclusive.offset.byteIdx
      (s.startInclusive.offset.byteIdx + n) =
      s.copy.toByteArray.extract 0 n := by
  have hse := Pos.Raw.le_iff.1 s.startInclusive_le_endExclusive
  rw [Slice.toByteArray_copy, ByteArray.extract_extract, Nat.add_zero,
    Nat.min_eq_left (by have := utf8ByteSize_eq (s := s); omega)]

theorem startsWith_iff {pat s : Slice} : startsWith pat s ↔ ∃ t, s.copy = pat.copy ++ t := by
  rw [startsWith]
  simp only [offset_startPos, -size_toByteArray]
  constructor
  · intro h
    split at h
    · rename_i h₁
      have h₂ := Internal.memcmpSlice_eq_true_iff.1 h
      simp only [Pos.Raw.byteIdx_offsetBy] at h₂
      rw [memcmpSlice_pat_eq_copy_toByteArray,
        memcmpSlice_s_eq_copy_extract (by simp [byteIdx_rawEndPos]; exact h₁)] at h₂
      rw [show pat.rawEndPos.byteIdx = pat.copy.utf8ByteSize from
        by simp [byteIdx_rawEndPos, Slice.utf8ByteSize_copy]] at h₂
      rw [← Slice.utf8ByteSize_copy (s := pat), ← Slice.utf8ByteSize_copy (s := s)] at h₁
      generalize pat.copy = pat' at *
      generalize s.copy = s' at *
      suffices pat'.rawEndPos.IsValid s' by
        have h₁' : (s'.sliceTo (s'.pos _ this)).copy = pat' := by
          simpa [← toByteArray_inj, copy_toByteArray_sliceTo]
        have := (s'.pos _ this).splits
        rw [h₁'] at this
        refine ⟨_, this.eq_append⟩
      rw [Pos.Raw.isValid_iff_isValidUTF8_extract_zero]
      refine ⟨by simpa using h₁, ?_⟩
      simpa [h₂] using pat'.isValidUTF8
    · simp at h
  · intro ⟨t, ht⟩
    have h₁ : pat.utf8ByteSize ≤ s.utf8ByteSize := by
      have := congrArg String.utf8ByteSize ht
      simp only [utf8ByteSize_append, Slice.utf8ByteSize_copy] at this
      omega
    simp only [dif_pos h₁, Internal.memcmpSlice_eq_true_iff, Pos.Raw.byteIdx_offsetBy]
    rw [memcmpSlice_pat_eq_copy_toByteArray,
      memcmpSlice_s_eq_copy_extract (n := pat.rawEndPos.byteIdx) h₁, byteIdx_rawEndPos, ht]
    simp only [-size_toByteArray, toByteArray_append]
    exact ByteArray.extract_append_eq_left (by simp)

theorem skipPrefix?_eq_some_iff {pat s : Slice} {pos : s.Pos} :
    skipPrefix? pat s = some pos ↔ (s.sliceTo pos).copy = pat.copy := by
  fun_cases skipPrefix? with
  | case1 h =>
    simp only [Option.some.injEq]
    obtain ⟨t, ht⟩ := startsWith_iff.1 h
    have hval : (pat.rawEndPos.offsetBy s.startPos.offset).IsValidForSlice s :=
      Pos.Raw.isValidForSlice_iff_exists_append.mpr ⟨pat.copy, t, ht, by
        ext
        simp only [Pos.Raw.byteIdx_offsetBy, offset_startPos, byteIdx_rawEndPos,
          String.byteIdx_rawEndPos, Slice.utf8ByteSize_copy]⟩
    have hsp : (s.pos _ hval).Splits pat.copy t := by
      refine ⟨ht, ?_⟩
      simp only [Pos.Raw.ext_iff, Slice.Pos.offset_copy, Pos.Raw.byteIdx_unoffsetBy,
        offset_pos, Pos.Raw.byteIdx_offsetBy, offset_startPos,
        byteIdx_rawEndPos, String.byteIdx_rawEndPos, Slice.utf8ByteSize_copy]
      omega
    rw [pos!_eq_pos hval]
    exact ⟨(· ▸ hsp.copy_sliceTo_eq), fun h => hsp.pos_eq (h ▸ pos.splits)⟩
  | case2 h =>
    simp only [startsWith_iff, not_exists] at h
    simp only [reduceCtorEq, false_iff]
    intro heq
    have := h (s.sliceFrom pos).copy
    simp [← heq, pos.splits.eq_append] at this

theorem isSome_skipPrefix? {pat s : Slice} : (skipPrefix? pat s).isSome = startsWith pat s := by
  fun_cases skipPrefix? <;> simp_all

public theorem startsWith_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    ForwardPattern.startsWith pat s = true := by
  suffices pat.copy = "" by simp [ForwardPattern.startsWith, startsWith_iff, this]
  simpa

public theorem skipPrefix?_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    ForwardPattern.skipPrefix? pat s = some s.startPos := by
  simpa [ForwardPattern.skipPrefix?, skipPrefix?_eq_some_iff]

end ForwardSliceSearcher

namespace Model.ForwardSliceSearcher

open Pattern.ForwardSliceSearcher

public instance {pat : Slice} : LawfulForwardPattern pat where
  skipPrefixOfNonempty?_eq _ := rfl
  startsWith_eq _ := isSome_skipPrefix?.symm

public theorem lawfulForwardPatternModel {pat : Slice} (hpat : pat.isEmpty = false) :
    LawfulForwardPatternModel pat where
  skipPrefix?_eq_some_iff pos := by
    simp [ForwardPattern.skipPrefix?, skipPrefix?_eq_some_iff, isLongestMatch_iff hpat]

end Model.ForwardSliceSearcher

namespace Model.ForwardStringSearcher

open Pattern.ForwardSliceSearcher

public instance {pat : String} : LawfulForwardPattern pat where
  skipPrefixOfNonempty?_eq _ := rfl
  startsWith_eq _ := isSome_skipPrefix?.symm

public theorem lawfulForwardPatternModel {pat : String} (hpat : pat ≠ "") :
    LawfulForwardPatternModel pat where
  skipPrefix?_eq_some_iff pos := by
    simp [ForwardPattern.skipPrefix?, skipPrefix?_eq_some_iff, isLongestMatch_iff hpat]

end Model.ForwardStringSearcher

namespace BackwardSliceSearcher

private theorem hs_ba_lemma {s : Slice} (hn : n ≤ s.utf8ByteSize) :
    s.str.toByteArray.extract (s.endExclusive.offset.byteIdx - n)
      s.endExclusive.offset.byteIdx =
      s.copy.toByteArray.extract (s.utf8ByteSize - n) s.utf8ByteSize := by
  have hsz := utf8ByteSize_eq (s := s)
  have hle := Pos.Raw.le_iff.1 s.startInclusive_le_endExclusive
  rw [Slice.toByteArray_copy, ByteArray.extract_extract,
    Nat.min_eq_left (by omega)]
  have h1 : s.endExclusive.offset.byteIdx - n =
      s.startInclusive.offset.byteIdx + (s.utf8ByteSize - n) := by omega
  have h2 : s.endExclusive.offset.byteIdx =
      s.startInclusive.offset.byteIdx + s.utf8ByteSize := by omega
  rw [← h1, ← h2]

theorem endsWith_iff {pat s : Slice} : endsWith pat s ↔ ∃ t, s.copy = t ++ pat.copy := by
  rw [endsWith]
  simp only [offset_startPos, offset_endPos, -size_toByteArray]
  have hse := Pos.Raw.le_iff.1 s.startInclusive_le_endExclusive
  have hpe := Pos.Raw.le_iff.1 pat.startInclusive_le_endExclusive
  constructor
  · intro h
    split at h
    · rename_i h₁
      have h₂ := Internal.memcmpSlice_eq_true_iff.1 h
      simp only [Pos.Raw.byteIdx_offsetBy, Pos.Raw.byteIdx_unoffsetBy, byteIdx_rawEndPos] at h₂
      have hpat_ba : pat.str.toByteArray.extract pat.startInclusive.offset.byteIdx
          (pat.startInclusive.offset.byteIdx + pat.utf8ByteSize) = pat.copy.toByteArray := by
        rw [show pat.startInclusive.offset.byteIdx + pat.utf8ByteSize =
          pat.endExclusive.offset.byteIdx from by simp [utf8ByteSize_eq]; omega]
        exact Slice.toByteArray_copy.symm
      rw [hpat_ba] at h₂
      have hle : pat.utf8ByteSize ≤ s.endExclusive.offset.byteIdx := by
        have := utf8ByteSize_eq (s := s); omega
      rw [Nat.sub_add_cancel hle] at h₂
      rw [hs_ba_lemma h₁] at h₂
      rw [← Slice.utf8ByteSize_copy (s := pat), ← Slice.utf8ByteSize_copy (s := s)] at h₁ h₂
      generalize pat.copy = pat' at *
      generalize s.copy = s' at *
      suffices (s'.rawEndPos.unoffsetBy pat'.rawEndPos).IsValid s' by
        have h₃ : (s'.sliceFrom (s'.pos _ this)).copy = pat' := by
          rw [← toByteArray_inj, (s'.pos _ this).splits.toByteArray_right_eq]
          simpa [offset_pos, Pos.Raw.byteIdx_unoffsetBy, byteIdx_rawEndPos]
        have := (s'.pos _ this).splits
        rw [h₃] at this
        exact ⟨_, this.eq_append⟩
      rw [Pos.Raw.isValid_iff_isValidUTF8_extract_utf8ByteSize]
      refine ⟨by simp [Pos.Raw.le_iff, Pos.Raw.byteIdx_unoffsetBy], ?_⟩
      simpa [Pos.Raw.byteIdx_unoffsetBy, byteIdx_rawEndPos, h₂] using pat'.isValidUTF8
    · simp at h
  · intro ⟨t, ht⟩
    have hpat_ba : pat.str.toByteArray.extract pat.startInclusive.offset.byteIdx
        (pat.startInclusive.offset.byteIdx + pat.utf8ByteSize) = pat.copy.toByteArray := by
      rw [show pat.startInclusive.offset.byteIdx + pat.utf8ByteSize =
        pat.endExclusive.offset.byteIdx from by simp [utf8ByteSize_eq]; omega]
      exact Slice.toByteArray_copy.symm
    have hsz : pat.utf8ByteSize ≤ s.utf8ByteSize := by
      have := congrArg String.utf8ByteSize ht
      simp only [utf8ByteSize_append, Slice.utf8ByteSize_copy] at this
      omega
    have hle : pat.utf8ByteSize ≤ s.endExclusive.offset.byteIdx := by
      have := utf8ByteSize_eq (s := s); omega
    simp only [dif_pos hsz, Internal.memcmpSlice_eq_true_iff, Pos.Raw.byteIdx_offsetBy,
      Pos.Raw.byteIdx_unoffsetBy, byteIdx_rawEndPos]
    rw [Nat.sub_add_cancel hle, hpat_ba, hs_ba_lemma hsz,
      show s.utf8ByteSize = s.copy.utf8ByteSize from Slice.utf8ByteSize_copy.symm,
      show pat.utf8ByteSize = pat.copy.utf8ByteSize from Slice.utf8ByteSize_copy.symm, ht]
    simp only [utf8ByteSize_append, Nat.add_sub_cancel]
    exact ByteArray.extract_append_eq_right (by simp) (by simp)

theorem skipSuffix?_eq_some_iff {pat s : Slice} {pos : s.Pos} :
    skipSuffix? pat s = some pos ↔ (s.sliceFrom pos).copy = pat.copy := by
  fun_cases skipSuffix? with
  | case1 h =>
    simp only [Option.some.injEq]
    obtain ⟨t, ht⟩ := endsWith_iff.1 h
    have hpc : pat.copy.utf8ByteSize = pat.utf8ByteSize := Slice.utf8ByteSize_copy
    have hsz : s.utf8ByteSize = t.utf8ByteSize + pat.utf8ByteSize := by
      have := congrArg String.utf8ByteSize ht
      simp only [utf8ByteSize_append, Slice.utf8ByteSize_copy] at this
      exact this
    have hoff : (s.endPos.offset.unoffsetBy pat.rawEndPos) =
        t.rawEndPos.offsetBy s.startInclusive.offset := by
      ext
      simp only [offset_endPos, Pos.Raw.byteIdx_unoffsetBy, byteIdx_rawEndPos,
        String.byteIdx_rawEndPos, Pos.Raw.byteIdx_offsetBy]
      have := Slice.utf8ByteSize_eq (s := s)
      have := Pos.Raw.le_iff.1 s.startInclusive_le_endExclusive
      omega
    have hval : (s.endPos.offset.unoffsetBy pat.rawEndPos).IsValidForSlice s :=
      Pos.Raw.isValidForSlice_iff_exists_append.mpr ⟨t, pat.copy, ht, hoff⟩
    have hsp : (s.pos _ hval).Splits t pat.copy := by
      refine ⟨ht, ?_⟩
      simp only [Pos.Raw.ext_iff, Slice.Pos.offset_copy, Pos.Raw.byteIdx_unoffsetBy,
        offset_pos, Pos.Raw.byteIdx_offsetBy, offset_endPos,
        byteIdx_rawEndPos, String.byteIdx_rawEndPos, Slice.utf8ByteSize_copy]
      have := Slice.utf8ByteSize_eq (s := s)
      have := Pos.Raw.le_iff.1 s.startInclusive_le_endExclusive
      omega
    rw [Slice.pos!_eq_pos hval]
    exact ⟨(· ▸ hsp.copy_sliceFrom_eq),
      fun h => hsp.pos_eq_of_eq_right (h ▸ pos.splits)⟩
  | case2 h =>
    simp only [endsWith_iff, not_exists] at h
    simp only [reduceCtorEq, false_iff]
    intro heq
    have := h (s.sliceTo pos).copy
    simp [← heq, pos.splits.eq_append] at this

theorem isSome_skipSuffix? {pat s : Slice} : (skipSuffix? pat s).isSome = endsWith pat s := by
  fun_cases skipSuffix? <;> simp_all

public theorem endsWith_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    BackwardPattern.endsWith pat s = true := by
  suffices pat.copy = "" by simp [BackwardPattern.endsWith, endsWith_iff, this]
  simpa

public theorem skipSuffix?_of_isEmpty {pat s : Slice} (hpat : pat.isEmpty = true) :
    BackwardPattern.skipSuffix? pat s = some s.endPos := by
  simpa [BackwardPattern.skipSuffix?, skipSuffix?_eq_some_iff]

end BackwardSliceSearcher

namespace Model.BackwardSliceSearcher

open Pattern.BackwardSliceSearcher

public instance {pat : Slice} : LawfulBackwardPattern pat where
  skipSuffixOfNonempty?_eq _ := rfl
  endsWith_eq _ := isSome_skipSuffix?.symm

public theorem lawfulBackwardPatternModel {pat : Slice} (hpat : pat.isEmpty = false) :
    LawfulBackwardPatternModel pat where
  skipSuffix?_eq_some_iff pos := by
    simp [BackwardPattern.skipSuffix?, skipSuffix?_eq_some_iff,
      ForwardSliceSearcher.isLongestRevMatch_iff hpat]

end Model.BackwardSliceSearcher

namespace Model.BackwardStringSearcher

open Pattern.BackwardSliceSearcher

public instance {pat : String} : LawfulBackwardPattern pat where
  skipSuffixOfNonempty?_eq _ := rfl
  endsWith_eq _ := isSome_skipSuffix?.symm

public theorem lawfulBackwardPatternModel {pat : String} (hpat : pat ≠ "") :
    LawfulBackwardPatternModel pat where
  skipSuffix?_eq_some_iff pos := by
    simp [BackwardPattern.skipSuffix?, skipSuffix?_eq_some_iff,
      ForwardStringSearcher.isLongestRevMatch_iff hpat]

end Model.BackwardStringSearcher

end Pattern

public theorem startsWith_string_eq_startsWith_toSlice {pat : String} {s : Slice} :
    s.startsWith pat = s.startsWith pat.toSlice := (rfl)

public theorem dropPrefix?_string_eq_dropPrefix?_toSlice {pat : String} {s : Slice} :
    s.dropPrefix? pat = s.dropPrefix? pat.toSlice := (rfl)

public theorem dropPrefix_string_eq_dropPrefix_toSlice {pat : String} {s : Slice} :
    s.dropPrefix pat = s.dropPrefix pat.toSlice := (rfl)

public theorem skipPrefix?_string_eq_skipPrefix?_toSlice {pat : String} {s : Slice} :
    s.skipPrefix? pat = s.skipPrefix? pat.toSlice := (rfl)

public theorem Pattern.ForwardPattern.skipPrefix?_string_eq_skipPrefix?_toSlice
    {pat : String} {s : Slice} :
    skipPrefix? pat s = skipPrefix? pat.toSlice s := (rfl)

public theorem Pos.skipWhile_string_eq_skipWhile_toSlice {pat : String} {s : Slice}
    (curr : s.Pos) :
    Pos.skipWhile curr pat = Pos.skipWhile curr pat.toSlice := by
  fun_induction Pos.skipWhile curr pat with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pattern.ForwardPattern.skipPrefix?_string_eq_skipPrefix?_toSlice, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pattern.ForwardPattern.skipPrefix?_string_eq_skipPrefix?_toSlice, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pattern.ForwardPattern.skipPrefix?_string_eq_skipPrefix?_toSlice]

public theorem skipPrefixWhile_string_eq_skipPrefixWhile_toSlice {pat : String} {s : Slice} :
    s.skipPrefixWhile pat = s.skipPrefixWhile pat.toSlice :=
  Pos.skipWhile_string_eq_skipWhile_toSlice s.startPos

public theorem dropWhile_string_eq_dropWhile_toSlice {pat : String} {s : Slice} :
    s.dropWhile pat = s.dropWhile pat.toSlice := by
  simp only [dropWhile]; exact congrArg _ skipPrefixWhile_string_eq_skipPrefixWhile_toSlice

public theorem takeWhile_string_eq_takeWhile_toSlice {pat : String} {s : Slice} :
    s.takeWhile pat = s.takeWhile pat.toSlice := by
  simp only [takeWhile]; exact congrArg _ skipPrefixWhile_string_eq_skipPrefixWhile_toSlice

public theorem all_string_eq_all_toSlice {pat : String} {s : Slice} :
    s.all pat = s.all pat.toSlice := by
  simp only [all, dropWhile_string_eq_dropWhile_toSlice]

public theorem endsWith_string_eq_endsWith_toSlice {pat : String} {s : Slice} :
    s.endsWith pat = s.endsWith pat.toSlice := (rfl)

public theorem skipSuffix?_string_eq_skipSuffix?_toSlice {pat : String} {s : Slice} :
    s.skipSuffix? pat = s.skipSuffix? pat.toSlice := (rfl)

public theorem dropSuffix?_string_eq_dropSuffix?_toSlice {pat : String} {s : Slice} :
    s.dropSuffix? pat = s.dropSuffix? pat.toSlice := (rfl)

public theorem dropSuffix_string_eq_dropSuffix_toSlice {pat : String} {s : Slice} :
    s.dropSuffix pat = s.dropSuffix pat.toSlice := (rfl)

public theorem Pattern.BackwardPattern.skipSuffix?_string_eq_skipSuffix?_toSlice
    {pat : String} {s : Slice} :
    skipSuffix? pat s = skipSuffix? pat.toSlice s := (rfl)

public theorem Pos.revSkipWhile_string_eq_revSkipWhile_toSlice {pat : String} {s : Slice}
    (curr : s.Pos) :
    Pos.revSkipWhile curr pat = Pos.revSkipWhile curr pat.toSlice := by
  fun_induction Pos.revSkipWhile curr pat with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pattern.BackwardPattern.skipSuffix?_string_eq_skipSuffix?_toSlice, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pattern.BackwardPattern.skipSuffix?_string_eq_skipSuffix?_toSlice, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pattern.BackwardPattern.skipSuffix?_string_eq_skipSuffix?_toSlice]

public theorem skipSuffixWhile_string_eq_skipSuffixWhile_toSlice {pat : String} {s : Slice} :
    s.skipSuffixWhile pat = s.skipSuffixWhile pat.toSlice :=
  Pos.revSkipWhile_string_eq_revSkipWhile_toSlice s.endPos

public theorem dropEndWhile_string_eq_dropEndWhile_toSlice {pat : String} {s : Slice} :
    s.dropEndWhile pat = s.dropEndWhile pat.toSlice := by
  simp only [dropEndWhile]; exact congrArg _ skipSuffixWhile_string_eq_skipSuffixWhile_toSlice

public theorem takeEndWhile_string_eq_takeEndWhile_toSlice {pat : String} {s : Slice} :
    s.takeEndWhile pat = s.takeEndWhile pat.toSlice := by
  simp only [takeEndWhile]; exact congrArg _ skipSuffixWhile_string_eq_skipSuffixWhile_toSlice

end String.Slice
