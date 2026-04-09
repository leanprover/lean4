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
import Init.Data.String.Lemmas.Intercalate
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.Splits
import Init.Data.ByteArray.Lemmas
import Init.Omega

public section

namespace String.Slice.Pattern.Model

namespace ForwardSliceSearcher

instance {pat : Slice} : PatternModel pat where
  Matches s := s = pat.copy

theorem strictPatternModel {pat : Slice} (hpat : pat.isEmpty = false) : StrictPatternModel pat where
  not_matches_empty := by simpa [PatternModel.Matches]

instance {pat : Slice} : NoPrefixPatternModel pat :=
  .of_length_eq (by simp +contextual [PatternModel.Matches])

instance {pat : Slice} : NoSuffixPatternModel pat :=
  .of_length_eq (by simp +contextual [PatternModel.Matches])

theorem isMatch_iff {pat s : Slice} {pos : s.Pos} :
    IsMatch pat pos ↔ (s.sliceTo pos).copy = pat.copy := by
  simp [Model.isMatch_iff, PatternModel.Matches]

theorem isRevMatch_iff {pat s : Slice} {pos : s.Pos} :
    IsRevMatch pat pos ↔ (s.sliceFrom pos).copy = pat.copy := by
  simp [Model.isRevMatch_iff, PatternModel.Matches]

theorem isLongestMatch_iff {pat s : Slice} {pos : s.Pos} :
    IsLongestMatch pat pos ↔ (s.sliceTo pos).copy = pat.copy := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestRevMatch_iff {pat s : Slice} {pos : s.Pos} :
    IsLongestRevMatch pat pos ↔ (s.sliceFrom pos).copy = pat.copy := by
  rw [isLongestRevMatch_iff_isRevMatch, isRevMatch_iff]

theorem isLongestMatchAt_iff {pat s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAt pat pos₁ pos₂ ↔ ∃ h, (s.slice pos₁ pos₂ h).copy = pat.copy := by
  simp [Model.isLongestMatchAt_iff, isLongestMatch_iff]

theorem isLongestMatchAtChain_iff {pat s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAtChain pat pos₁ pos₂ ↔
      ∃ h n, (s.slice pos₁ pos₂ h).copy = String.join (List.replicate n pat.copy) := by
  refine ⟨fun h => ⟨h.le, ?_⟩, fun ⟨h, n, h'⟩ => ?_⟩
  · induction h with
    | nil => simpa using ⟨0, by simp⟩
    | cons p₁ p₂ p₃ h₁ h₂ ih =>
      rw [isLongestMatchAt_iff] at h₁
      obtain ⟨n, ih⟩ := ih
      obtain ⟨h₀, h₁⟩ := h₁
      have : (s.slice p₁ p₃ (Std.le_trans h₀ h₂.le)).copy = (s.slice p₁ p₂ h₀).copy ++ (s.slice p₂ p₃ h₂.le).copy := by
        simp [(Slice.Pos.slice p₂ _ _ h₀ h₂.le).splits.eq_append]
      refine ⟨n + 1, ?_⟩
      rw [this, h₁, ih]
      simp [← String.join_cons, ← List.replicate_succ]
  · induction n generalizing pos₁ pos₂ with
    | zero => simp_all
    | succ n ih =>
      rw [List.replicate_succ, String.join_cons] at h'
      refine .cons _ (Pos.ofSlice (Pos.ofEqAppend h')) _ ?_ (ih ?_ Pos.ofSlice_le ?_)
      · simpa [isLongestMatchAt_iff] using (Pos.splits_ofEqAppend h').copy_sliceTo_eq
      · simpa [sliceFrom_slice ▸ (Pos.splits_ofEqAppend h').copy_sliceFrom_eq] using ⟨n, rfl⟩
      · simpa using (Pos.splits_ofEqAppend h').copy_sliceFrom_eq

theorem isLongestMatchAtChain_startPos_endPos_iff {pat s : Slice} :
    IsLongestMatchAtChain pat s.startPos s.endPos ↔
      ∃ n, s.copy = String.join (List.replicate n pat.copy) := by
  simp [isLongestMatchAtChain_iff]

theorem isLongestRevMatchAt_iff {pat s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestRevMatchAt pat pos₁ pos₂ ↔ ∃ h, (s.slice pos₁ pos₂ h).copy = pat.copy := by
  simp [Model.isLongestRevMatchAt_iff, isLongestRevMatch_iff]

theorem isLongestRevMatchAtChain_iff {pat s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestRevMatchAtChain pat pos₁ pos₂ ↔
      ∃ h n, (s.slice pos₁ pos₂ h).copy = String.join (List.replicate n pat.copy) := by
  refine ⟨fun h => ⟨h.le, ?_⟩, fun ⟨h, n, h'⟩ => ?_⟩
  · induction h with
    | nil => simpa using ⟨0, by simp⟩
    | cons p₂ p₃ h₁ h₂ ih =>
      rw [isLongestRevMatchAt_iff] at h₂
      obtain ⟨n, ih⟩ := ih
      obtain ⟨h₀, h₂⟩ := h₂
      have : (s.slice pos₁ p₃ (Std.le_trans h₁.le h₀)).copy = (s.slice pos₁ p₂ h₁.le).copy ++ (s.slice p₂ p₃ h₀).copy := by
        simp [(Slice.Pos.slice p₂ _ _ (IsLongestRevMatchAtChain.le ‹_›) h₀).splits.eq_append]
      refine ⟨n + 1, ?_⟩
      rw [this, h₂, ih]
      simp [← List.replicate_append_replicate]
  · induction n generalizing pos₁ pos₂ with
    | zero => simp_all
    | succ n ih =>
      have h'' : (s.slice pos₁ pos₂ h).copy = String.join (List.replicate n pat.copy) ++ pat.copy := by
        rw [h', List.replicate_succ', String.join_append]; simp
      refine .cons _ (Pos.ofSlice (Pos.ofEqAppend h'')) _ (ih ?_ Pos.le_ofSlice ?_) ?_
      · simpa [sliceTo_slice ▸ (Pos.splits_ofEqAppend h'').copy_sliceTo_eq] using ⟨n, rfl⟩
      · simpa using (Pos.splits_ofEqAppend h'').copy_sliceTo_eq
      · simpa [isLongestRevMatchAt_iff] using (Pos.splits_ofEqAppend h'').copy_sliceFrom_eq

theorem isLongestRevMatchAtChain_startPos_endPos_iff {pat s : Slice} :
    IsLongestRevMatchAtChain pat s.startPos s.endPos ↔
      ∃ n, s.copy = String.join (List.replicate n pat.copy) := by
  simp [isLongestRevMatchAtChain_iff]

theorem isLongestMatchAt_iff_splits {pat s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAt pat pos₁ pos₂ ↔ ∃ t₁ t₂, pos₁.Splits t₁ (pat.copy ++ t₂) ∧
      pos₂.Splits (t₁ ++ pat.copy) t₂ := by
  simp only [isLongestMatchAt_iff, copy_slice_eq_iff_splits]

theorem isLongestRevMatchAt_iff_splits {pat s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestRevMatchAt pat pos₁ pos₂ ↔ ∃ t₁ t₂, pos₁.Splits t₁ (pat.copy ++ t₂) ∧
      pos₂.Splits (t₁ ++ pat.copy) t₂ := by
  simp only [isLongestRevMatchAt_iff, copy_slice_eq_iff_splits]

theorem isLongestMatch_iff_splits {pat s : Slice} {pos : s.Pos} :
    IsLongestMatch pat pos ↔ ∃ t, pos.Splits pat.copy t := by
  rw [isLongestMatch_iff, copy_sliceTo_eq_iff_exists_splits]

theorem isLongestRevMatch_iff_splits {pat s : Slice} {pos : s.Pos} :
    IsLongestRevMatch pat pos ↔ ∃ t, pos.Splits t pat.copy := by
  rw [isLongestRevMatch_iff, copy_sliceFrom_eq_iff_exists_splits]

theorem isLongestMatchAt_iff_extract {pat s : Slice} {pos₁ pos₂ : s.Pos} (h : pat.isEmpty = false) :
    IsLongestMatchAt pat pos₁ pos₂ ↔
      s.copy.toByteArray.extract pos₁.offset.byteIdx pos₂.offset.byteIdx = pat.copy.toByteArray := by
  rw [isLongestMatchAt_iff]
  refine ⟨fun ⟨h, h'⟩ => ?_, fun h' => ?_⟩
  · simp [← h', toByteArray_copy_slice]
  · rw [← Slice.toByteArray_copy_ne_empty_iff, ← h', ne_eq, ByteArray.extract_eq_empty_iff] at h
    exact ⟨by simp [Pos.le_iff, Pos.Raw.le_iff]; omega,
      by simp [← h', ← toByteArray_inj, toByteArray_copy_slice]⟩

theorem isLongestRevMatchAt_iff_extract {pat s : Slice} {pos₁ pos₂ : s.Pos}
    (h : pat.isEmpty = false) :
    IsLongestRevMatchAt pat pos₁ pos₂ ↔
      s.copy.toByteArray.extract pos₁.offset.byteIdx pos₂.offset.byteIdx =
        pat.copy.toByteArray := by
  rw [isLongestRevMatchAt_iff]
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

theorem offset_of_isLongestRevMatchAt {pat s : Slice} {pos₁ pos₂ : s.Pos}
    (h : pat.isEmpty = false) (h' : IsLongestRevMatchAt pat pos₁ pos₂) :
    pos₂.offset = pos₁.offset.increaseBy pat.utf8ByteSize := by
  simp only [Pos.Raw.ext_iff, Pos.Raw.byteIdx_increaseBy]
  rw [isLongestRevMatchAt_iff_extract h] at h'
  rw [← Slice.toByteArray_copy_ne_empty_iff, ← h', ne_eq, ByteArray.extract_eq_empty_iff] at h
  replace h' := congrArg ByteArray.size h'
  simp only [ByteArray.size_extract, size_toByteArray, utf8ByteSize_copy] at h'
  suffices pos₂.offset.byteIdx ≤ s.utf8ByteSize by omega
  simpa [Pos.le_iff, Pos.Raw.le_iff] using pos₂.le_endPos

theorem matchesAt_iff_splits {pat s : Slice} {pos : s.Pos} :
    MatchesAt pat pos ↔ ∃ t₁ t₂, pos.Splits t₁ (pat.copy ++ t₂) := by
  simp only [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_splits]
  exact ⟨fun ⟨e, t₁, t₂, ht₁, ht₂⟩ => ⟨t₁, t₂, ht₁⟩,
    fun ⟨t₁, t₂, ht⟩ => ⟨ht.rotateRight, t₁, t₂, ht, ht.splits_rotateRight⟩⟩

theorem revMatchesAt_iff_splits {pat s : Slice} {pos : s.Pos} :
    RevMatchesAt pat pos ↔ ∃ t₁ t₂, pos.Splits (t₁ ++ pat.copy) t₂ := by
  simp only [revMatchesAt_iff_exists_isLongestRevMatchAt, isLongestRevMatchAt_iff_splits]
  exact ⟨fun ⟨e, t₁, t₂, ht₁, ht₂⟩ => ⟨t₁, t₂, ht₂⟩,
    fun ⟨t₁, t₂, ht⟩ => ⟨ht.rotateLeft, t₁, t₂, ht.splits_rotateLeft, ht⟩⟩

theorem exists_matchesAt_iff_eq_append {pat s : Slice} :
    (∃ (pos : s.Pos), MatchesAt pat pos) ↔ ∃ t₁ t₂, s.copy = t₁ ++ pat.copy ++ t₂ := by
  simp only [matchesAt_iff_splits]
  constructor
  · rintro ⟨pos, t₁, t₂, hsplit⟩
    exact ⟨t₁, t₂, by rw [hsplit.eq_append, append_assoc]⟩
  · rintro ⟨t₁, t₂, heq⟩
    have hvalid : t₁.rawEndPos.IsValidForSlice s :=
      Pos.Raw.isValidForSlice_iff_exists_append.mpr
        ⟨t₁, pat.copy ++ t₂, by rw [← append_assoc]; exact heq, rfl⟩
    exact ⟨s.pos _ hvalid, t₁, t₂, ⟨by rw [← append_assoc]; exact heq, by simp⟩⟩

theorem exists_revMatchesAt_iff_eq_append {pat s : Slice} :
    (∃ (pos : s.Pos), RevMatchesAt pat pos) ↔ ∃ t₁ t₂, s.copy = t₁ ++ pat.copy ++ t₂ := by
  simp only [revMatchesAt_iff_splits]
  constructor
  · rintro ⟨pos, t₁, t₂, hsplit⟩
    exact ⟨t₁, t₂, by rw [hsplit.eq_append, append_assoc]⟩
  · rintro ⟨t₁, t₂, heq⟩
    have hvalid : (t₁ ++ pat.copy).rawEndPos.IsValidForSlice s :=
      Pos.Raw.isValidForSlice_iff_exists_append.mpr
        ⟨t₁ ++ pat.copy, t₂, heq, rfl⟩
    exact ⟨s.pos _ hvalid, t₁, t₂, ⟨heq, by simp⟩⟩

theorem matchesAt_iff_isLongestMatchAt {pat s : Slice} {pos : s.Pos} (h : pat.isEmpty = false) :
    MatchesAt pat pos ↔ ∃ (h : (pos.offset.increaseBy pat.utf8ByteSize).IsValidForSlice s),
      IsLongestMatchAt pat pos (s.pos _ h) := by
  refine ⟨fun ⟨⟨p, h'⟩⟩ => ?_, fun ⟨_, h⟩ => ⟨⟨_, h⟩⟩⟩
  have := offset_of_isLongestMatchAt h h' ▸ p.isValidForSlice
  refine ⟨this, ?_⟩
  obtain rfl : p = s.pos _ this := by simpa [Pos.ext_iff] using offset_of_isLongestMatchAt h h'
  exact h'

theorem revMatchesAt_iff_isLongestRevMatchAt {pat s : Slice} {pos : s.Pos}
    (h : pat.isEmpty = false) :
    RevMatchesAt pat pos ↔
      ∃ (h : (pos.offset.decreaseBy pat.utf8ByteSize).IsValidForSlice s),
        IsLongestRevMatchAt pat (s.pos _ h) pos := by
  refine ⟨fun ⟨⟨p, h'⟩⟩ => ?_, fun ⟨_, h⟩ => ⟨⟨_, h⟩⟩⟩
  have hoff := offset_of_isLongestRevMatchAt h h'
  have hvalid : (pos.offset.decreaseBy pat.utf8ByteSize).IsValidForSlice s := by
    rw [show pos.offset.decreaseBy pat.utf8ByteSize = p.offset from by
      simp [Pos.Raw.ext_iff, Pos.Raw.byteIdx_decreaseBy, Pos.Raw.byteIdx_increaseBy] at hoff ⊢
      omega]
    exact p.isValidForSlice
  refine ⟨hvalid, ?_⟩
  obtain rfl : p = s.pos _ hvalid := by
    simp only [Pos.ext_iff, offset_pos]
    simp [Pos.Raw.ext_iff, Pos.Raw.byteIdx_decreaseBy, Pos.Raw.byteIdx_increaseBy] at hoff ⊢
    omega
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

instance {pat : String} : PatternModel pat where
  Matches s := s = pat

theorem strictPatternModel {pat : String} (h : pat ≠ "") : StrictPatternModel pat where
  not_matches_empty := by simpa [PatternModel.Matches]

instance {pat : String} : NoPrefixPatternModel pat :=
  .of_length_eq (by simp +contextual [PatternModel.Matches])

instance {pat : String} : NoSuffixPatternModel pat :=
  .of_length_eq (by simp +contextual [PatternModel.Matches])

theorem isMatch_iff_slice {pat : String} {s : Slice} {pos : s.Pos} :
    IsMatch (ρ := String) pat pos ↔ IsMatch (ρ := Slice) pat.toSlice pos := by
  simp only [Model.isMatch_iff, PatternModel.Matches, copy_toSlice]

theorem isRevMatch_iff_slice {pat : String} {s : Slice} {pos : s.Pos} :
    IsRevMatch (ρ := String) pat pos ↔ IsRevMatch (ρ := Slice) pat.toSlice pos := by
  simp only [Model.isRevMatch_iff, PatternModel.Matches, copy_toSlice]

theorem isLongestMatch_iff_isLongestMatch_toSlice {pat : String} {s : Slice} {pos : s.Pos} :
    IsLongestMatch (ρ := String) pat pos ↔ IsLongestMatch (ρ := Slice) pat.toSlice pos where
  mp h := ⟨isMatch_iff_slice.1 h.isMatch, fun p hp hm => h.not_isMatch p hp (isMatch_iff_slice.2 hm)⟩
  mpr h := ⟨isMatch_iff_slice.2 h.isMatch, fun p hp hm => h.not_isMatch p hp (isMatch_iff_slice.1 hm)⟩

theorem isLongestRevMatch_iff_isLongestRevMatch_toSlice {pat : String} {s : Slice} {pos : s.Pos} :
    IsLongestRevMatch (ρ := String) pat pos ↔ IsLongestRevMatch (ρ := Slice) pat.toSlice pos where
  mp h := ⟨isRevMatch_iff_slice.1 h.isRevMatch,
    fun p hp hm => h.not_isRevMatch p hp (isRevMatch_iff_slice.2 hm)⟩
  mpr h := ⟨isRevMatch_iff_slice.2 h.isRevMatch,
    fun p hp hm => h.not_isRevMatch p hp (isRevMatch_iff_slice.1 hm)⟩

theorem isLongestMatchAt_iff_isLongestMatchAt_toSlice {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAt (ρ := String) pat pos₁ pos₂ ↔
      IsLongestMatchAt (ρ := Slice) pat.toSlice pos₁ pos₂ := by
  simp [Model.isLongestMatchAt_iff, isLongestMatch_iff_isLongestMatch_toSlice]

theorem isLongestMatchAtChain_iff_isLongestMatchAtChain_toSlice {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAtChain pat pos₁ pos₂ ↔
      IsLongestMatchAtChain pat.toSlice pos₁ pos₂ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | nil => simp
    | cons p₁ p₂ p₃ h₁ h₂ ih =>
      exact .cons _ _ _ (isLongestMatchAt_iff_isLongestMatchAt_toSlice.1 h₁) ih
  · induction h with
    | nil => simp
    | cons p₁ p₂ p₃ h₁ h₂ ih =>
      exact .cons _ _ _ (isLongestMatchAt_iff_isLongestMatchAt_toSlice.2 h₁) ih

theorem isLongestMatchAtChain_iff {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAtChain pat pos₁ pos₂ ↔
      ∃ h n, (s.slice pos₁ pos₂ h).copy = String.join (List.replicate n pat) := by
  simp [isLongestMatchAtChain_iff_isLongestMatchAtChain_toSlice,
    ForwardSliceSearcher.isLongestMatchAtChain_iff]

theorem isLongestMatchAtChain_startPos_endPos_iff {pat : String} {s : Slice} :
    IsLongestMatchAtChain pat s.startPos s.endPos ↔
      ∃ n, s.copy = String.join (List.replicate n pat) := by
  simp [isLongestMatchAtChain_iff]

theorem isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice {pat : String} {s : Slice}
    {pos₁ pos₂ : s.Pos} :
    IsLongestRevMatchAt (ρ := String) pat pos₁ pos₂ ↔
      IsLongestRevMatchAt (ρ := Slice) pat.toSlice pos₁ pos₂ := by
  simp [Model.isLongestRevMatchAt_iff, isLongestRevMatch_iff_isLongestRevMatch_toSlice]

theorem isLongestRevMatchAtChain_iff_isLongestRevMatchAtChain_toSlice {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestRevMatchAtChain pat pos₁ pos₂ ↔
      IsLongestRevMatchAtChain pat.toSlice pos₁ pos₂ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | nil => simp
    | cons p₂ p₃ _ hmatch ih =>
      exact .cons _ _ _ ih (isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice.1 hmatch)
  · induction h with
    | nil => simp
    | cons p₂ p₃ _ hmatch ih =>
      exact .cons _ _ _ ih (isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice.2 hmatch)

theorem isLongestRevMatchAtChain_iff {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestRevMatchAtChain pat pos₁ pos₂ ↔
      ∃ h n, (s.slice pos₁ pos₂ h).copy = String.join (List.replicate n pat) := by
  simp [isLongestRevMatchAtChain_iff_isLongestRevMatchAtChain_toSlice,
    ForwardSliceSearcher.isLongestRevMatchAtChain_iff]

theorem isLongestRevMatchAtChain_startPos_endPos_iff {pat : String} {s : Slice} :
    IsLongestRevMatchAtChain pat s.startPos s.endPos ↔
      ∃ n, s.copy = String.join (List.replicate n pat) := by
  simp [isLongestRevMatchAtChain_iff]

theorem matchesAt_iff_toSlice {pat : String} {s : Slice} {pos : s.Pos} :
    MatchesAt (ρ := String) pat pos ↔ MatchesAt (ρ := Slice) pat.toSlice pos := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_isLongestMatchAt_toSlice]

theorem revMatchesAt_iff_toSlice {pat : String} {s : Slice} {pos : s.Pos} :
    RevMatchesAt (ρ := String) pat pos ↔ RevMatchesAt (ρ := Slice) pat.toSlice pos := by
  simp [revMatchesAt_iff_exists_isLongestRevMatchAt,
    isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice]

theorem isMatch_iff {pat : String} {s : Slice} {pos : s.Pos} :
    IsMatch pat pos ↔ (s.sliceTo pos).copy = pat := by
  rw [isMatch_iff_slice, ForwardSliceSearcher.isMatch_iff]
  simp

theorem isRevMatch_iff {pat : String} {s : Slice} {pos : s.Pos} :
    IsRevMatch pat pos ↔ (s.sliceFrom pos).copy = pat := by
  rw [isRevMatch_iff_slice, ForwardSliceSearcher.isRevMatch_iff]
  simp

theorem isLongestMatch_iff {pat : String} {s : Slice} {pos : s.Pos} :
    IsLongestMatch pat pos ↔ (s.sliceTo pos).copy = pat := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestRevMatch_iff {pat : String} {s : Slice} {pos : s.Pos} :
    IsLongestRevMatch pat pos ↔ (s.sliceFrom pos).copy = pat := by
  rw [isLongestRevMatch_iff_isRevMatch, isRevMatch_iff]

theorem isLongestMatchAt_iff {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAt pat pos₁ pos₂ ↔ ∃ h, (s.slice pos₁ pos₂ h).copy = pat := by
  rw [isLongestMatchAt_iff_isLongestMatchAt_toSlice,
    ForwardSliceSearcher.isLongestMatchAt_iff]
  simp

theorem isLongestRevMatchAt_iff {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestRevMatchAt pat pos₁ pos₂ ↔ ∃ h, (s.slice pos₁ pos₂ h).copy = pat := by
  rw [isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice,
    ForwardSliceSearcher.isLongestRevMatchAt_iff]
  simp

theorem isLongestMatchAt_iff_splits {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAt pat pos₁ pos₂ ↔
      ∃ t₁ t₂, pos₁.Splits t₁ (pat ++ t₂) ∧ pos₂.Splits (t₁ ++ pat) t₂ := by
  rw [isLongestMatchAt_iff_isLongestMatchAt_toSlice,
    ForwardSliceSearcher.isLongestMatchAt_iff_splits]
  simp

theorem isLongestRevMatchAt_iff_splits {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestRevMatchAt pat pos₁ pos₂ ↔
      ∃ t₁ t₂, pos₁.Splits t₁ (pat ++ t₂) ∧ pos₂.Splits (t₁ ++ pat) t₂ := by
  rw [isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice,
    ForwardSliceSearcher.isLongestRevMatchAt_iff_splits]
  simp

theorem isLongestMatchAt_iff_extract {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos} (h : pat ≠ "") :
    IsLongestMatchAt pat pos₁ pos₂ ↔
      s.copy.toByteArray.extract pos₁.offset.byteIdx pos₂.offset.byteIdx = pat.toByteArray := by
  rw [isLongestMatchAt_iff_isLongestMatchAt_toSlice,
    ForwardSliceSearcher.isLongestMatchAt_iff_extract (by simpa)]
  simp

theorem isLongestRevMatchAt_iff_extract {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos}
    (h : pat ≠ "") :
    IsLongestRevMatchAt pat pos₁ pos₂ ↔
      s.copy.toByteArray.extract pos₁.offset.byteIdx pos₂.offset.byteIdx = pat.toByteArray := by
  rw [isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice,
    ForwardSliceSearcher.isLongestRevMatchAt_iff_extract (by simpa)]
  simp

theorem offset_of_isLongestMatchAt {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos}
    (h : pat ≠ "") (h' : IsLongestMatchAt pat pos₁ pos₂) :
    pos₂.offset = pos₁.offset.increaseBy pat.utf8ByteSize := by
  rw [show pat.utf8ByteSize = pat.toSlice.utf8ByteSize from utf8ByteSize_toSlice.symm]
  exact ForwardSliceSearcher.offset_of_isLongestMatchAt (by simpa)
    (isLongestMatchAt_iff_isLongestMatchAt_toSlice.1 h')

theorem offset_of_isLongestRevMatchAt {pat : String} {s : Slice} {pos₁ pos₂ : s.Pos}
    (h : pat ≠ "") (h' : IsLongestRevMatchAt pat pos₁ pos₂) :
    pos₂.offset = pos₁.offset.increaseBy pat.utf8ByteSize := by
  rw [show pat.utf8ByteSize = pat.toSlice.utf8ByteSize from utf8ByteSize_toSlice.symm]
  exact ForwardSliceSearcher.offset_of_isLongestRevMatchAt (by simpa)
    (isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice.1 h')

theorem matchesAt_iff_splits {pat : String} {s : Slice} {pos : s.Pos} :
    MatchesAt pat pos ↔ ∃ t₁ t₂, pos.Splits t₁ (pat ++ t₂) := by
  rw [matchesAt_iff_toSlice,
    ForwardSliceSearcher.matchesAt_iff_splits]
  simp

theorem revMatchesAt_iff_splits {pat : String} {s : Slice} {pos : s.Pos} :
    RevMatchesAt pat pos ↔ ∃ t₁ t₂, pos.Splits (t₁ ++ pat) t₂ := by
  rw [revMatchesAt_iff_toSlice,
    ForwardSliceSearcher.revMatchesAt_iff_splits]
  simp

theorem exists_matchesAt_iff_eq_append {pat : String} {s : Slice} :
    (∃ (pos : s.Pos), MatchesAt pat pos) ↔ ∃ t₁ t₂, s.copy = t₁ ++ pat ++ t₂ := by
  simp only [matchesAt_iff_splits]
  constructor
  · rintro ⟨pos, t₁, t₂, hsplit⟩
    exact ⟨t₁, t₂, by rw [hsplit.eq_append, append_assoc]⟩
  · rintro ⟨t₁, t₂, heq⟩
    have hvalid : t₁.rawEndPos.IsValidForSlice s :=
      Pos.Raw.isValidForSlice_iff_exists_append.mpr
        ⟨t₁, pat ++ t₂, by rw [← append_assoc]; exact heq, rfl⟩
    exact ⟨s.pos _ hvalid, t₁, t₂, ⟨by rw [← append_assoc]; exact heq, by simp⟩⟩

theorem exists_revMatchesAt_iff_eq_append {pat : String} {s : Slice} :
    (∃ (pos : s.Pos), RevMatchesAt pat pos) ↔ ∃ t₁ t₂, s.copy = t₁ ++ pat ++ t₂ := by
  rw [show (∃ (pos : s.Pos), RevMatchesAt (ρ := String) pat pos) ↔
      (∃ (pos : s.Pos), RevMatchesAt (ρ := Slice) pat.toSlice pos) from by
    simp [revMatchesAt_iff_toSlice],
    ForwardSliceSearcher.exists_revMatchesAt_iff_eq_append]
  simp

theorem matchesAt_iff_isLongestMatchAt {pat : String} {s : Slice} {pos : s.Pos}
    (h : pat ≠ "") :
    MatchesAt pat pos ↔ ∃ (h : (pos.offset.increaseBy pat.utf8ByteSize).IsValidForSlice s),
      IsLongestMatchAt pat pos (s.pos _ h) := by
  have key := ForwardSliceSearcher.matchesAt_iff_isLongestMatchAt (pat := pat.toSlice)
    (by simpa) (pos := pos)
  simp only [utf8ByteSize_toSlice, ← isLongestMatchAt_iff_isLongestMatchAt_toSlice] at key
  rwa [matchesAt_iff_toSlice]

theorem revMatchesAt_iff_isLongestRevMatchAt {pat : String} {s : Slice} {pos : s.Pos}
    (h : pat ≠ "") :
    RevMatchesAt pat pos ↔
      ∃ (h : (pos.offset.decreaseBy pat.utf8ByteSize).IsValidForSlice s),
        IsLongestRevMatchAt pat (s.pos _ h) pos := by
  have key := ForwardSliceSearcher.revMatchesAt_iff_isLongestRevMatchAt (pat := pat.toSlice)
    (by simpa) (pos := pos)
  simp only [utf8ByteSize_toSlice, ← isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice] at key
  rwa [revMatchesAt_iff_toSlice]

theorem matchesAt_iff_getElem {pat : String} {s : Slice} {pos : s.Pos} (h : pat ≠ "") :
    MatchesAt pat pos ↔
      ∃ (h : pos.offset.byteIdx + pat.toByteArray.size ≤ s.copy.toByteArray.size),
        ∀ (j), (hj : j < pat.toByteArray.size) →
          pat.toByteArray[j] = s.copy.toByteArray[pos.offset.byteIdx + j] := by
  have key := ForwardSliceSearcher.matchesAt_iff_getElem (pat := pat.toSlice)
    (by simpa) (pos := pos)
  simp only [copy_toSlice] at key
  rwa [matchesAt_iff_toSlice]

theorem le_of_matchesAt {pat : String} {s : Slice} {pos : s.Pos} (h : pat ≠ "")
    (h' : MatchesAt pat pos) : pos.offset.increaseBy pat.utf8ByteSize ≤ s.rawEndPos := by
  rw [show pat.utf8ByteSize = pat.toSlice.utf8ByteSize from utf8ByteSize_toSlice.symm]
  exact ForwardSliceSearcher.le_of_matchesAt (by simpa)
    (matchesAt_iff_toSlice.1 h')

theorem matchesAt_iff_matchesAt_toSlice {pat : String} {s : Slice}
    {pos : s.Pos} : MatchesAt pat pos ↔ MatchesAt pat.toSlice pos := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_isLongestMatchAt_toSlice]

theorem revMatchesAt_iff_revMatchesAt_toSlice {pat : String} {s : Slice}
    {pos : s.Pos} : RevMatchesAt pat pos ↔ RevMatchesAt pat.toSlice pos := by
  simp [revMatchesAt_iff_exists_isLongestRevMatchAt,
    isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice]

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

theorem isValidRevSearchFrom_iff_isValidRevSearchFrom_toSlice {pat : String}
    {s : Slice} {pos : s.Pos} {l : List (SearchStep s)} :
    IsValidRevSearchFrom pat pos l ↔ IsValidRevSearchFrom pat.toSlice pos l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | startPos => simpa using IsValidRevSearchFrom.startPos
    | matched => simp_all [IsValidRevSearchFrom.matched,
        isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice]
    | mismatched => simp_all [IsValidRevSearchFrom.mismatched, revMatchesAt_iff_revMatchesAt_toSlice]
  · induction h with
    | startPos => simpa using IsValidRevSearchFrom.startPos
    | matched => simp_all [IsValidRevSearchFrom.matched,
        isLongestRevMatchAt_iff_isLongestRevMatchAt_toSlice]
    | mismatched => simp_all [IsValidRevSearchFrom.mismatched, revMatchesAt_iff_revMatchesAt_toSlice]

end ForwardStringSearcher

end String.Slice.Pattern.Model
