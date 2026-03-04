/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.String
public import Init.Data.String.Lemmas.Pattern.Basic
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.String.Lemmas.Basic
import Init.Data.ByteArray.Lemmas
import Init.Omega

public section

namespace String.Slice.Pattern.Model

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
  simp only [Model.isMatch_iff, ForwardPatternModel.Matches, ne_eq, copy_eq_empty_iff,
    Bool.not_eq_true, and_iff_right_iff_imp]
  intro h'
  rw [← isEmpty_copy (s := s.sliceTo pos), h', isEmpty_copy, h]

theorem isLongestMatch_iff {pat s : Slice} {pos : s.Pos} (h : pat.isEmpty = false) :
    IsLongestMatch pat pos ↔ (s.sliceTo pos).copy = pat.copy := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff h]

theorem isLongestMatchAt_iff {pat s : Slice} {pos₁ pos₂ : s.Pos} (h : pat.isEmpty = false) :
    IsLongestMatchAt pat pos₁ pos₂ ↔ ∃ h, (s.slice pos₁ pos₂ h).copy = pat.copy := by
  simp [Model.isLongestMatchAt_iff, isLongestMatch_iff h]

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

theorem offset_of_isLongestMatchAt {pat s : Slice} {pos₁ pos₂ : s.Pos} (h : pat.isEmpty = false)
    (h' : IsLongestMatchAt pat pos₁ pos₂) : pos₂.offset = pos₁.offset.increaseBy pat.utf8ByteSize := by
  simp only [Pos.Raw.ext_iff, Pos.Raw.byteIdx_increaseBy]
  rw [isLongestMatchAt_iff_extract h] at h'
  rw [← Slice.toByteArray_copy_ne_empty_iff, ← h', ne_eq, ByteArray.extract_eq_empty_iff] at h
  replace h' := congrArg ByteArray.size h'
  simp only [ByteArray.size_extract, size_toByteArray, utf8ByteSize_copy] at h'
  suffices pos₂.offset.byteIdx ≤ s.utf8ByteSize by omega
  simpa [Pos.le_iff, Pos.Raw.le_iff] using pos₂.le_endPos

theorem matchesAt_iff_splits {pat s : Slice} {pos : s.Pos} (h : pat.isEmpty = false) :
    MatchesAt pat pos ↔ ∃ t₁ t₂, pos.Splits t₁ (pat.copy ++ t₂) := by
  simp only [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_splits h]
  exact ⟨fun ⟨e, t₁, t₂, ht₁, ht₂⟩ => ⟨t₁, t₂, ht₁⟩,
    fun ⟨t₁, t₂, ht⟩ => ⟨ht.rotateRight, t₁, t₂, ht, ht.splits_rotateRight⟩⟩

theorem exists_matchesAt_iff_eq_append {pat s : Slice} (h : pat.isEmpty = false) :
    (∃ (pos : s.Pos), MatchesAt pat pos) ↔ ∃ t₁ t₂, s.copy = t₁ ++ pat.copy ++ t₂ := by
  simp only [matchesAt_iff_splits h]
  constructor
  · rintro ⟨pos, t₁, t₂, hsplit⟩
    exact ⟨t₁, t₂, by rw [hsplit.eq_append, append_assoc]⟩
  · rintro ⟨t₁, t₂, heq⟩
    have hvalid : t₁.rawEndPos.IsValidForSlice s :=
      Pos.Raw.isValidForSlice_iff_exists_append.mpr
        ⟨t₁, pat.copy ++ t₂, by rw [← append_assoc]; exact heq, rfl⟩
    exact ⟨s.pos _ hvalid, t₁, t₂, ⟨by rw [← append_assoc]; exact heq, by simp⟩⟩

theorem matchesAt_iff_isLongestMatchAt {pat s : Slice} {pos : s.Pos} (h : pat.isEmpty = false) :
    MatchesAt pat pos ↔ ∃ (h : (pos.offset.increaseBy pat.utf8ByteSize).IsValidForSlice s),
      IsLongestMatchAt pat pos (s.pos _ h) := by
  refine ⟨fun ⟨⟨p, h'⟩⟩ => ?_, fun ⟨_, h⟩ => ⟨⟨_, h⟩⟩⟩
  have := offset_of_isLongestMatchAt h h' ▸ p.isValidForSlice
  refine ⟨this, ?_⟩
  obtain rfl : p = s.pos _ this := by simpa [Pos.ext_iff] using offset_of_isLongestMatchAt h h'
  exact h'

theorem matchesAt_iff_getElem {pat s : Slice} {pos : s.Pos} (h : pat.isEmpty = false) :
    MatchesAt pat pos ↔
      ∃ (h : pos.offset.byteIdx + pat.copy.toByteArray.size ≤ s.copy.toByteArray.size),
        ∀ (j), (hj : j < pat.copy.toByteArray.size) →
          pat.copy.toByteArray[j] = s.copy.toByteArray[pos.offset.byteIdx + j] := by
  rw [matchesAt_iff_isLongestMatchAt h]
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun ⟨h₁, h₂⟩ => ?_⟩
  · refine ⟨by simpa using h₁.le_utf8ByteSize, fun j hj => ?_⟩
    rw [isLongestMatchAt_iff_extract h] at h₂
    replace h₂ := congrArg (·[j]?) h₂
    simp only [offset_pos, Pos.Raw.byteIdx_increaseBy] at h₂
    rw [getElem?_pos, getElem?_pos, ByteArray.getElem_extract] at h₂
    · simpa using h₂.symm
    · have := h₁.le_utf8ByteSize
      simp only [Pos.Raw.byteIdx_increaseBy, size_toByteArray, utf8ByteSize_copy,
        ByteArray.size_extract, gt_iff_lt] at this ⊢ hj
      omega
  · suffices s.copy.toByteArray.extract pos.offset.byteIdx
        (pos.offset.byteIdx + pat.copy.toByteArray.size) = pat.copy.toByteArray by
      have h₀ := (((Pos.Raw.isValidUTF8_extract_iff _ _ ?_ ?_).1
        (this ▸ pat.copy.isValidUTF8)).resolve_left ?_).2
      · exact ⟨by simpa using h₀, (isLongestMatchAt_iff_extract h).2 (by simpa using this)⟩
      · simp [Pos.Raw.le_iff]
      · simpa [Pos.Raw.le_iff] using h₁
      · simpa [Pos.Raw.ext_iff, ← Slice.isEmpty_iff]
    refine ByteArray.ext_getElem ?_ (fun i hi hi' => ?_)
    · simp only [size_toByteArray, utf8ByteSize_copy, ByteArray.size_extract] at ⊢ h₁
      omega
    · simp [ByteArray.getElem_extract, h₂]

theorem le_of_matchesAt {pat s : Slice} {pos : s.Pos} (h : pat.isEmpty = false)
    (h' : MatchesAt pat pos) : pos.offset.increaseBy pat.utf8ByteSize ≤ s.rawEndPos := by
  simpa [Pos.Raw.le_iff] using ((matchesAt_iff_getElem h).1 h').1

end ForwardSliceSearcher

namespace ForwardStringSearcher

instance {pat : String} : ForwardPatternModel pat where
  Matches s := s ≠ "" ∧ s = pat
  not_matches_empty := by simp

instance {pat : String} : NoPrefixForwardPatternModel pat :=
  .of_length_eq (by simp +contextual [ForwardPatternModel.Matches])

theorem isMatch_iff_slice {pat : String} {s : Slice} {pos : s.Pos} :
    IsMatch (ρ := String) pat pos ↔ IsMatch (ρ := Slice) pat.toSlice pos := by
  simp only [Model.isMatch_iff, ForwardPatternModel.Matches, copy_toSlice]

theorem isLongestMatch_iff_isLongestMatch_toSlice {pat : String} {s : Slice} {pos : s.Pos} :
    IsLongestMatch (ρ := String) pat pos ↔ IsLongestMatch (ρ := Slice) pat.toSlice pos where
  mp h := ⟨isMatch_iff_slice.1 h.isMatch, fun p hp hm => h.not_isMatch p hp (isMatch_iff_slice.2 hm)⟩
  mpr h := ⟨isMatch_iff_slice.2 h.isMatch, fun p hp hm => h.not_isMatch p hp (isMatch_iff_slice.1 hm)⟩

theorem isLongestMatchAt_iff_isLongestMatchAt_toSlice {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAt (ρ := String) pat pos₁ pos₂ ↔
      IsLongestMatchAt (ρ := Slice) pat.toSlice pos₁ pos₂ := by
  simp [Model.isLongestMatchAt_iff, isLongestMatch_iff_isLongestMatch_toSlice]

theorem matchesAt_iff_toSlice {pat : String} {s : Slice} {pos : s.Pos} :
    MatchesAt (ρ := String) pat pos ↔ MatchesAt (ρ := Slice) pat.toSlice pos := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_isLongestMatchAt_toSlice]

private theorem toSlice_isEmpty (h : pat ≠ "") : pat.toSlice.isEmpty = false := by
  rwa [isEmpty_toSlice, isEmpty_eq_false_iff]

theorem isMatch_iff {pat : String} {s : Slice} {pos : s.Pos} (h : pat ≠ "") :
    IsMatch pat pos ↔ (s.sliceTo pos).copy = pat := by
  rw [isMatch_iff_slice, ForwardSliceSearcher.isMatch_iff (toSlice_isEmpty h)]
  simp

theorem isLongestMatch_iff {pat : String} {s : Slice} {pos : s.Pos} (h : pat ≠ "") :
    IsLongestMatch pat pos ↔ (s.sliceTo pos).copy = pat := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff h]

theorem isLongestMatchAt_iff {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} (h : pat ≠ "") :
    IsLongestMatchAt pat pos₁ pos₂ ↔ ∃ h, (s.slice pos₁ pos₂ h).copy = pat := by
  rw [isLongestMatchAt_iff_isLongestMatchAt_toSlice,
    ForwardSliceSearcher.isLongestMatchAt_iff (toSlice_isEmpty h)]
  simp

theorem isLongestMatchAt_iff_splits {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos}
    (h : pat ≠ "") :
    IsLongestMatchAt pat pos₁ pos₂ ↔
      ∃ t₁ t₂, pos₁.Splits t₁ (pat ++ t₂) ∧ pos₂.Splits (t₁ ++ pat) t₂ := by
  rw [isLongestMatchAt_iff_isLongestMatchAt_toSlice,
    ForwardSliceSearcher.isLongestMatchAt_iff_splits (toSlice_isEmpty h)]
  simp

theorem isLongestMatchAt_iff_extract {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos}
    (h : pat ≠ "") :
    IsLongestMatchAt pat pos₁ pos₂ ↔
      s.copy.toByteArray.extract pos₁.offset.byteIdx pos₂.offset.byteIdx = pat.toByteArray := by
  rw [isLongestMatchAt_iff_isLongestMatchAt_toSlice,
    ForwardSliceSearcher.isLongestMatchAt_iff_extract (toSlice_isEmpty h)]
  simp

theorem offset_of_isLongestMatchAt {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos}
    (h : pat ≠ "") (h' : IsLongestMatchAt pat pos₁ pos₂) :
    pos₂.offset = pos₁.offset.increaseBy pat.utf8ByteSize := by
  rw [show pat.utf8ByteSize = pat.toSlice.utf8ByteSize from utf8ByteSize_toSlice.symm]
  exact ForwardSliceSearcher.offset_of_isLongestMatchAt (toSlice_isEmpty h)
    (isLongestMatchAt_iff_isLongestMatchAt_toSlice.1 h')

theorem matchesAt_iff_splits {pat : String} {s : Slice} {pos : s.Pos} (h : pat ≠ "") :
    MatchesAt pat pos ↔ ∃ t₁ t₂, pos.Splits t₁ (pat ++ t₂) := by
  rw [matchesAt_iff_toSlice,
    ForwardSliceSearcher.matchesAt_iff_splits (toSlice_isEmpty h)]
  simp

theorem exists_matchesAt_iff_eq_append {pat : String} {s : Slice} (h : pat ≠ "") :
    (∃ (pos : s.Pos), MatchesAt pat pos) ↔ ∃ t₁ t₂, s.copy = t₁ ++ pat ++ t₂ := by
  simp only [matchesAt_iff_splits h]
  constructor
  · rintro ⟨pos, t₁, t₂, hsplit⟩
    exact ⟨t₁, t₂, by rw [hsplit.eq_append, append_assoc]⟩
  · rintro ⟨t₁, t₂, heq⟩
    have hvalid : t₁.rawEndPos.IsValidForSlice s :=
      Pos.Raw.isValidForSlice_iff_exists_append.mpr
        ⟨t₁, pat ++ t₂, by rw [← append_assoc]; exact heq, rfl⟩
    exact ⟨s.pos _ hvalid, t₁, t₂, ⟨by rw [← append_assoc]; exact heq, by simp⟩⟩

theorem matchesAt_iff_isLongestMatchAt {pat : String} {s : Slice} {pos : s.Pos}
    (h : pat ≠ "") :
    MatchesAt pat pos ↔ ∃ (h : (pos.offset.increaseBy pat.utf8ByteSize).IsValidForSlice s),
      IsLongestMatchAt pat pos (s.pos _ h) := by
  have key := ForwardSliceSearcher.matchesAt_iff_isLongestMatchAt (pat := pat.toSlice)
    (toSlice_isEmpty h) (pos := pos)
  simp only [utf8ByteSize_toSlice, ← isLongestMatchAt_iff_isLongestMatchAt_toSlice] at key
  rwa [matchesAt_iff_toSlice]

theorem matchesAt_iff_getElem {pat : String} {s : Slice} {pos : s.Pos} (h : pat ≠ "") :
    MatchesAt pat pos ↔
      ∃ (h : pos.offset.byteIdx + pat.toByteArray.size ≤ s.copy.toByteArray.size),
        ∀ (j), (hj : j < pat.toByteArray.size) →
          pat.toByteArray[j] = s.copy.toByteArray[pos.offset.byteIdx + j] := by
  have key := ForwardSliceSearcher.matchesAt_iff_getElem (pat := pat.toSlice)
    (toSlice_isEmpty h) (pos := pos)
  simp only [copy_toSlice] at key
  rwa [matchesAt_iff_toSlice]

theorem le_of_matchesAt {pat : String} {s : Slice} {pos : s.Pos} (h : pat ≠ "")
    (h' : MatchesAt pat pos) : pos.offset.increaseBy pat.utf8ByteSize ≤ s.rawEndPos := by
  rw [show pat.utf8ByteSize = pat.toSlice.utf8ByteSize from utf8ByteSize_toSlice.symm]
  exact ForwardSliceSearcher.le_of_matchesAt (toSlice_isEmpty h)
    (matchesAt_iff_toSlice.1 h')

theorem matchesAt_iff_matchesAt_toSlice {pat : String} {s : Slice}
    {pos : s.Pos} : MatchesAt pat pos ↔ MatchesAt pat.toSlice pos := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_isLongestMatchAt_toSlice]

theorem toSearcher_eq {pat : String} {s : Slice} :
    ToForwardSearcher.toSearcher pat s = ToForwardSearcher.toSearcher pat.toSlice s := (rfl)

theorem isValidSearchFrom_iff_isValidSearchFrom_toSlice {pat : String}
    {s : Slice} {pos : s.Pos} {l : List (SearchStep s)} :
    IsValidSearchFrom pat pos l ↔ IsValidSearchFrom pat.toSlice pos l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | endPos => simpa using IsValidSearchFrom.endPos
    | matched => simp_all [IsValidSearchFrom.matched, isLongestMatchAt_iff_isLongestMatchAt_toSlice]
    | mismatched => simp_all [IsValidSearchFrom.mismatched, matchesAt_iff_matchesAt_toSlice]
  · induction h with
    | endPos => simpa using IsValidSearchFrom.endPos
    | matched => simp_all [IsValidSearchFrom.matched, isLongestMatchAt_iff_isLongestMatchAt_toSlice]
    | mismatched => simp_all [IsValidSearchFrom.mismatched, matchesAt_iff_matchesAt_toSlice]

end ForwardStringSearcher

end String.Slice.Pattern.Model
