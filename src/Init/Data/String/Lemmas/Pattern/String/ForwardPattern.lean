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

theorem skipPrefix?_eq_some_iff {pat s : Slice} {pos : s.Pos} :
    skipPrefix? pat s = some pos ↔ (s.sliceTo pos).copy = pat.copy := by
  fun_cases skipPrefix? with
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
    simp [← heq, -sliceTo_append_sliceFrom, pos.splits.eq_append] at this

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

public instance {pat : Slice} : LawfulForwardPatternModel pat where
  skipPrefixOfNonempty?_eq _ := rfl
  startsWith_eq _ := isSome_skipPrefix?.symm
  skipPrefix?_eq_some_iff pos := by
    simp [ForwardPattern.skipPrefix?, skipPrefix?_eq_some_iff, isLongestMatch_iff]

end Model.ForwardSliceSearcher

namespace Model.ForwardStringSearcher

open Pattern.ForwardSliceSearcher

public instance {pat : String} : LawfulForwardPatternModel pat where
  skipPrefixOfNonempty?_eq _ := rfl
  startsWith_eq _ := isSome_skipPrefix?.symm
  skipPrefix?_eq_some_iff pos := by
    simp [ForwardPattern.skipPrefix?, skipPrefix?_eq_some_iff, isLongestMatch_iff]

end Model.ForwardStringSearcher

namespace BackwardSliceSearcher

theorem endsWith_iff {pat s : Slice} : endsWith pat s ↔ ∃ t, s.copy = t ++ pat.copy := by
  rw [endsWith]
  simp [Internal.memcmpSlice_eq_true_iff, utf8ByteSize_eq_size_toByteArray_copy, -size_toByteArray]
  generalize pat.copy = pat
  generalize s.copy = s
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, ?_⟩
  · rw [Nat.sub_add_cancel h₁] at h₂
    suffices (s.rawEndPos.unoffsetBy pat.rawEndPos).IsValid s by
      have h₃ : (s.sliceFrom (s.pos _ this)).copy = pat := by
        rw [← toByteArray_inj, (s.pos _ this).splits.toByteArray_right_eq]
        simpa [offset_pos, Pos.Raw.byteIdx_unoffsetBy, byteIdx_rawEndPos]
      have := (s.pos _ this).splits
      rw [h₃] at this
      exact ⟨_, this.eq_append⟩
    rw [Pos.Raw.isValid_iff_isValidUTF8_extract_utf8ByteSize]
    refine ⟨by simp [Pos.Raw.le_iff, Pos.Raw.byteIdx_unoffsetBy], ?_⟩
    simp only [size_toByteArray] at h₂
    simpa [Pos.Raw.byteIdx_unoffsetBy, byteIdx_rawEndPos, h₂] using pat.isValidUTF8
  · rintro ⟨t, rfl⟩
    exact ⟨by simp, by rw [Nat.sub_add_cancel (by simp)]; exact
      ByteArray.extract_append_eq_right (by simp) (by simp)⟩

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
    have hoff : (s.endPos.offset.unoffsetBy pat.rawEndPos) = t.rawEndPos := by
      ext
      simp only [offset_endPos, Pos.Raw.byteIdx_unoffsetBy, byteIdx_rawEndPos,
        String.byteIdx_rawEndPos]
      omega
    have hval : (s.endPos.offset.unoffsetBy pat.rawEndPos).IsValidForSlice s :=
      Pos.Raw.isValidForSlice_iff_exists_append.mpr ⟨t, pat.copy, ht, hoff⟩
    have hsp : (s.pos _ hval).Splits t pat.copy := ⟨ht, hoff⟩
    rw [Slice.pos!_eq_pos hval]
    exact ⟨(· ▸ hsp.copy_sliceFrom_eq),
      fun h => hsp.pos_eq_of_eq_right (h ▸ pos.splits)⟩
  | case2 h =>
    simp only [endsWith_iff, not_exists] at h
    simp only [reduceCtorEq, false_iff]
    intro heq
    have := h (s.sliceTo pos).copy
    simp [← heq, -sliceTo_append_sliceFrom, pos.splits.eq_append] at this

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

public instance {pat : Slice} : LawfulBackwardPatternModel pat where
  skipSuffixOfNonempty?_eq _ := rfl
  endsWith_eq _ := isSome_skipSuffix?.symm
  skipSuffix?_eq_some_iff pos := by
    simp [BackwardPattern.skipSuffix?, skipSuffix?_eq_some_iff,
      ForwardSliceSearcher.isLongestRevMatch_iff]

end Model.BackwardSliceSearcher

namespace Model.BackwardStringSearcher

open Pattern.BackwardSliceSearcher

public instance {pat : String} : LawfulBackwardPatternModel pat where
  skipSuffixOfNonempty?_eq _ := rfl
  endsWith_eq _ := isSome_skipSuffix?.symm
  skipSuffix?_eq_some_iff pos := by
    simp [BackwardPattern.skipSuffix?, skipSuffix?_eq_some_iff,
      ForwardStringSearcher.isLongestRevMatch_iff]

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

public theorem Pos.skip?_string_eq_skip?_toSlice {pat : String} {s : Slice} {pos : s.Pos} :
    pos.skip? pat = pos.skip? pat.toSlice := (rfl)

public theorem Pos.skipWhile_string_eq_skipWhile_toSlice {pat : String} {s : Slice}
    (curr : s.Pos) :
    Pos.skipWhile curr pat = Pos.skipWhile curr pat.toSlice := by
  fun_induction Pos.skipWhile curr pat with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pos.skip?_string_eq_skip?_toSlice, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pos.skip?_string_eq_skip?_toSlice, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pos.skip?_string_eq_skip?_toSlice, h]

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
  simp only [all, skipPrefixWhile_string_eq_skipPrefixWhile_toSlice]

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

public theorem Pos.revSkip?_string_eq_revSkip?_toSlice {pat : String} {s : Slice} {pos : s.Pos} :
    pos.revSkip? pat = pos.revSkip? pat.toSlice := (rfl)

public theorem Pos.revSkipWhile_string_eq_revSkipWhile_toSlice {pat : String} {s : Slice}
    (curr : s.Pos) :
    Pos.revSkipWhile curr pat = Pos.revSkipWhile curr pat.toSlice := by
  fun_induction Pos.revSkipWhile curr pat with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pos.revSkip?_string_eq_revSkip?_toSlice, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pos.revSkip?_string_eq_revSkip?_toSlice, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pos.revSkip?_string_eq_revSkip?_toSlice, h]

public theorem skipSuffixWhile_string_eq_skipSuffixWhile_toSlice {pat : String} {s : Slice} :
    s.skipSuffixWhile pat = s.skipSuffixWhile pat.toSlice :=
  Pos.revSkipWhile_string_eq_revSkipWhile_toSlice s.endPos

public theorem dropEndWhile_string_eq_dropEndWhile_toSlice {pat : String} {s : Slice} :
    s.dropEndWhile pat = s.dropEndWhile pat.toSlice := by
  simp only [dropEndWhile]; exact congrArg _ skipSuffixWhile_string_eq_skipSuffixWhile_toSlice

public theorem takeEndWhile_string_eq_takeEndWhile_toSlice {pat : String} {s : Slice} :
    s.takeEndWhile pat = s.takeEndWhile pat.toSlice := by
  simp only [takeEndWhile]; exact congrArg _ skipSuffixWhile_string_eq_skipSuffixWhile_toSlice

public theorem revAll_string_eq_revAll_toSlice {pat : String} {s : Slice} :
    s.revAll pat = s.revAll pat.toSlice := by
  simp [revAll, skipSuffixWhile_string_eq_skipSuffixWhile_toSlice]

end String.Slice
