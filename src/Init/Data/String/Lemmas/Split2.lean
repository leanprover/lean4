/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Basic
public import Init.Data.String.Subslice
public import Init.Data.String.Lemmas.Splits
public import Init.Data.String.Slice
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.Basic
import all Init.Data.String.Pattern.String
import all Init.Data.String.Defs
import Init.Data.String.Lemmas.IsEmpty
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Termination
import Init.Data.ByteArray.Lemmas
import Init.Data.String.Lemmas.Order
import Init.Data.String.OrderInstances
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.Vector.Lemmas
import Init.Grind
import Init.Data.Iterators.Lemmas.Basic
public import Init.Data.String.Lemmas.Pattern

public section

namespace String

@[simp]
theorem Pos.Raw.isValidForSlice_zero {s : Slice} : (0 : Pos.Raw).IsValidForSlice s where
  le_rawEndPos := by simp [Pos.Raw.le_iff]
  isValid_offsetBy := by simpa using s.startInclusive.isValid

end String

namespace String.Slice

@[simp]
theorem Pos.isValidForSlice_offset {s : Slice} {p : s.Pos} : p.offset.IsValidForSlice s :=
  p.isValidForSlice

@[simp]
theorem pos_rawEndPos {s : Slice} : s.pos s.rawEndPos Pos.Raw.isValidForSlice_rawEndPos = s.endPos := by
  simp [Pos.ext_iff]

theorem Slice.splits_next_startPos {s : Slice} {h : s.startPos ≠ s.endPos} :
    (s.startPos.next h).Splits (singleton (s.startPos.get h)) (s.sliceFrom (s.startPos.next h)).copy := by
  rw [← String.empty_append (s := singleton (s.startPos.get h))]
  apply Slice.Pos.Splits.next
  have := Slice.Pos.splits_next_right s.startPos h
  rwa [copy_sliceTo_startPos] at this

@[simp]
theorem copy_pos {s : Slice} {p : Pos.Raw} {h : Pos.Raw.IsValidForSlice s p} :
    (s.pos p h).copy = s.copy.pos p (Pos.Raw.isValid_copy_iff.2 h) := by
  simp [String.Pos.ext_iff]

@[simp]
theorem _root_.String.cast_pos {s t : String} {p : Pos.Raw} {h : Pos.Raw.IsValid s p} {h' : s = t} :
    (s.pos p h).cast h' = t.pos p (h' ▸ h) := by
  simp [String.Pos.ext_iff]

theorem Pos.ne_of_lt {s : Slice} {p q : s.Pos} : p < q → p ≠ q := by
  simpa [Pos.ext_iff, Pos.Raw.ext_iff, Pos.lt_iff, Pos.Raw.lt_iff] using Nat.ne_of_lt

theorem Pos.Splits.copy_sliceTo_eq {s : Slice} {p : s.Pos} (h : p.Splits t₁ t₂) :
    (s.sliceTo p).copy = t₁ :=
  p.splits.eq_left h

theorem Pos.Splits.copy_sliceFrom_eq {s : Slice} {p : s.Pos} (h : p.Splits t₁ t₂) :
    (s.sliceFrom p).copy = t₂ :=
  p.splits.eq_right h

theorem _root_.String.Pos.splits_append_rawEndPos {s t : String} :
    ((s ++ t).pos s.rawEndPos ((Pos.Raw.isValid_rawEndPos).append_right t)).Splits s t where
  eq_append := rfl
  offset_eq_rawEndPos := rfl

theorem pos!_eq_pos {s : Slice} {p : Pos.Raw} (h : p.IsValidForSlice s) :
    s.pos! p = s.pos p h := by
  simp [Slice.pos!, h]

theorem _root_.String.pos!_eq_pos {s : String} {p : Pos.Raw} (h : p.IsValid s) :
    s.pos! p = s.pos p h := by
  rw [String.pos!, Slice.pos!_eq_pos h.toSlice, String.pos]

section BEq

@[simp]
theorem beq_eq_true_iff {s t : Slice} : s == t ↔ s.copy = t.copy := by
  simp only [BEq.beq, beq]
  split <;> rename_i h
  · rw [Pattern.Internal.memcmpSlice_eq_true_iff]
    simp only [offset_startPos, Pos.Raw.byteIdx_zero, Pos.Raw.offsetBy_zero, byteIdx_rawEndPos]
    rw (occs := [2]) [h]
    rw [utf8ByteSize_eq_size_toByteArray_copy, ByteArray.extract_zero_size,
      utf8ByteSize_eq_size_toByteArray_copy, ByteArray.extract_zero_size, String.toByteArray_inj]
  · simpa using ne_of_apply_ne String.utf8ByteSize (by simpa)

@[simp]
theorem beq_eq_false_iff {s t : Slice} : (s == t) = false ↔ s.copy ≠ t.copy := by
  simp [← Bool.not_eq_true]

theorem beq_eq_decide {s t : Slice} : (s == t) = decide (s.copy = t.copy) := by
  cases h : s == t <;> simp_all

end BEq

namespace Pattern


/-
Is there a correctness statement for searching beyond what I already have???
-/

@[ext]
structure SplitFrom {s : Slice} (startPos : s.Pos) where
  l : List s.Subslice
  any_head? : l.head?.any (·.startInclusive = startPos)

def SplitFrom.at {s : Slice} (pos : s.Pos) : SplitFrom pos where
  l := [s.subslice pos pos (Slice.Pos.le_refl _)]
  any_head? := by simp

@[simp]
theorem SplitFrom.l_at {s : Slice} (pos : s.Pos) :
    (SplitFrom.at pos).l = [s.subslice pos pos (Slice.Pos.le_refl _)] := (rfl)

def SplitFrom.append {s : Slice} {p₁ p₂ : s.Pos} (l₁ : SplitFrom p₁) (l₂ : SplitFrom p₂) :
    SplitFrom p₁ where
  l := l₁.l ++ l₂.l
  any_head? := by simpa using Option.any_or_of_any_left l₁.any_head?

@[simp]
theorem SplitFrom.l_append {s : Slice} {p₁ p₂ : s.Pos} {l₁ : SplitFrom p₁} {l₂ : SplitFrom p₂} :
    (l₁.append l₂).l = l₁.l ++ l₂.l :=
  (rfl)

def SplitFrom.extend {s : Slice} (p₁ : s.Pos) {p₂ : s.Pos} (h : p₁ ≤ p₂) (l : SplitFrom p₂) :
    SplitFrom p₁ where
  l :=
    match l.l, l.any_head? with
    | st :: sts, h => st.extendLeft p₁ (by simp_all) :: sts
  any_head? := by split; simp

@[simp]
theorem SplitFrom.l_extend {s : Slice} {p₁ p₂ : s.Pos} (h : p₁ ≤ p₂) {l : SplitFrom p₂} :
    (l.extend p₁ h).l = match l.l, l.any_head? with | st :: sts, h => st.extendLeft p₁ (by simp_all) :: sts := (rfl)

@[simp]
theorem SplitFrom.extend_self {s : Slice} {p₁ : s.Pos} (l : SplitFrom p₁) :
    l.extend p₁ (Slice.Pos.le_refl _) = l := by
  rcases l with ⟨l, h⟩
  match l, h with
  | st :: sts, h =>
    simp at h
    simp [SplitFrom.extend, ← h]

@[simp]
theorem SplitFrom.extend_extend {s : Slice} {p₀ p₁ p₂ : s.Pos} {h : p₀ ≤ p₁} {h' : p₁ ≤ p₂}
    {l : SplitFrom p₂} : (l.extend p₁ h').extend p₀ h = l.extend p₀ (Slice.Pos.le_trans h h') := by
  rcases l with ⟨l, h⟩
  match l, h with
  | st :: sts, h => simp [SplitFrom.extend]

open Classical in
noncomputable def dropPrefixAt?Model {ρ : Type} (pat : ρ) [ForwardPatternModel pat] {s : Slice}
    (start : s.Pos) : Option s.Pos :=
  if h : ∃ pos, IsLongestMatchAt pat start pos then some h.choose else none

theorem dropPrefixAt?Model_eq_none_of_not_matchesAt {ρ : Type} {pat : ρ} [ForwardPatternModel pat]
    {s : Slice} {start : s.Pos} (h : ¬ MatchesAt pat start) :
    dropPrefixAt?Model pat start = none := by
  rw [dropPrefixAt?Model, dif_neg]
  simp only [not_exists]
  exact fun p hp => h ⟨⟨_, hp⟩⟩

theorem isLongestMatchAt_of_dropPrefixAt?Model_eq_some {ρ : Type} {pat : ρ} [ForwardPatternModel pat]
    {s : Slice} {pos pos' : s.Pos} (h : dropPrefixAt?Model pat pos = some pos') :
    IsLongestMatchAt pat pos pos' := by
  simp [dropPrefixAt?Model] at h
  obtain ⟨h, rfl⟩ := h
  exact Exists.choose_spec _

theorem dropPrefixAt?Model_eq_some_of_isLongestMatchAt {ρ : Type} {pat : ρ} [ForwardPatternModel pat]
    {s : Slice} {pos pos' : s.Pos} (h : IsLongestMatchAt pat pos pos') :
    dropPrefixAt?Model pat pos = some pos' := by
  have h₀ : ∃ p, IsLongestMatchAt pat pos p := ⟨_, h⟩
  have : ∃ p, dropPrefixAt?Model pat pos = some p ∧ IsLongestMatchAt pat pos p := by
    simpa [dropPrefixAt?Model, h₀] using Exists.choose_spec _
  obtain ⟨p, h₁, h₂⟩ := this
  rw [h₁, Option.some.injEq, h₂.eq h]

theorem lt_of_dropPrefixAt?Model_eq_some {ρ : Type} {pat : ρ} [ForwardPatternModel pat]
    {s : Slice} {pos pos' : s.Pos} (h : dropPrefixAt?Model pat pos = some pos') : pos < pos' :=
  isLongestMatchAt_of_dropPrefixAt?Model_eq_some h |>.lt

noncomputable def splitModel {ρ : Type} (pat : ρ) [ForwardPatternModel pat] {s : Slice}
    (start : s.Pos) : SplitFrom start :=
  if h : start = s.endPos then
    SplitFrom.at start
  else
    match hd : dropPrefixAt?Model pat start with
    | some pos =>
      have : start < pos := lt_of_dropPrefixAt?Model_eq_some hd
      (SplitFrom.at start).append (splitModel pat pos)
    | none => SplitFrom.extend start (by simp) (splitModel pat (start.next h))
termination_by start

theorem splitModel_eq_of_isLongestMatchAt {ρ : Type} {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {start stop : s.Pos} (h : IsLongestMatchAt pat start stop) :
    splitModel pat start = (SplitFrom.at start).append (splitModel pat stop) := by
  rw [splitModel, dif_neg (Slice.Pos.ne_endPos_of_lt h.lt)]
  split
  · rename_i p heq
    simp [dropPrefixAt?Model_eq_some_of_isLongestMatchAt h] at heq
    congr <;> exact heq.symm
  · rename_i heq
    simp [dropPrefixAt?Model_eq_some_of_isLongestMatchAt h] at heq

theorem splitModel_eq_of_not_matchesAt {ρ : Type} {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {start stop : s.Pos} (h₀ : start ≤ stop) (h : ∀ p, start ≤ p → p < stop → ¬ MatchesAt pat p) :
    splitModel pat start = (SplitFrom.extend start h₀ (splitModel pat stop)) := by
  induction start using WellFounded.induction Slice.Pos.wellFounded_gt with | h start ih
  by_cases h' : start < stop
  · rw [splitModel, dif_neg (Slice.Pos.ne_endPos_of_lt h')]
    have : ¬ MatchesAt pat start := h start (Slice.Pos.le_refl _) h'
    split
    · rename_i heq
      simp [dropPrefixAt?Model_eq_none_of_not_matchesAt this] at heq
    · rw [ih, SplitFrom.extend_extend]
      · simp
      · simp [h']
      · refine fun p hp₁ hp₂ => h p (Std.le_of_lt (by simpa using hp₁)) hp₂
  · obtain rfl : start = stop := Std.le_antisymm h₀ (Std.not_lt.1 h')
    rw [SplitFrom.extend_self]

def splitOnLists {s : Slice} (currPos : s.Pos) (l : List (SearchStep s)) : List s.Subslice :=
  match l with
  | [] => [s.subsliceFrom currPos]
  | .rejected .. :: l => splitOnLists currPos l
  | .matched p q :: l => s.subslice! currPos p :: splitOnLists q l

theorem IsValidSearchFrom.splitOnLists_eq_splitModel {ρ : Type} (pat : ρ) [ForwardPatternModel pat]
    (l : List (SearchStep s)) (pos pos' : s.Pos) (h₀ : pos ≤ pos')
    (h' : ∀ p, pos ≤ p → p < pos' → ¬ MatchesAt pat p)
    (h : IsValidSearchFrom pat pos' l) :
    splitOnLists pos l = ((splitModel pat pos').extend pos h₀).l := by
  induction h generalizing pos with
  | endPos =>
    simp [splitOnLists, splitModel]
    split
    simp_all only [SplitFrom.l_at, List.cons.injEq, List.nil_eq, List.head?_cons, Option.any_some,
      decide_eq_true_eq, heq_eq_eq, and_true]
    rename_i h
    simp only [← h.1]
    ext <;> simp
  | matched h valid ih =>
    rename_i l startPos endPos
    simp only [splitOnLists]
    rw [subslice!_eq_subslice h₀, splitModel_eq_of_isLongestMatchAt h]
    simp [SplitFrom.at, SplitFrom.append]
    refine ⟨?_, ?_⟩
    · ext <;> simp
    · rw [ih endPos (Slice.Pos.le_refl _), SplitFrom.extend_self]
      intro p hp₁ hp₂
      exact False.elim (Std.lt_irrefl (Std.lt_of_le_of_lt hp₁ hp₂))
  | mismatched h rej valid ih =>
    simp only [splitOnLists]
    rename_i l startPos endPos
    rw [splitModel_eq_of_not_matchesAt (Std.le_of_lt h) rej,
      SplitFrom.extend_extend]
    rw [ih]
    intro p hp₁ hp₂
    by_cases hp : p < startPos
    · exact h' p hp₁ hp
    · exact rej _ (Std.not_lt.1 hp) hp₂

theorem toList_eq_splitOnLists' {ρ : Type} {pat : ρ} {σ : Slice → Type} [ToForwardSearcher pat σ]
    [∀ s, Std.Iterator (σ s) Id (SearchStep s)] [∀ s, Std.Iterators.Finite (σ s) Id] {s : Slice}
    (it : Std.Iter (α := σ s) (SearchStep s)) (currPos : s.Pos) :
    (Std.Iter.mk (α := SplitIterator pat s) (.operating currPos it)).toList =
      splitOnLists currPos it.toList := by
  induction it using Std.Iter.inductSteps generalizing currPos with | step it ihy ihs
  rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
  conv => rhs; rw [Std.Iter.toList_eq_match_step]
  simp [Std.Iter.toIterM]
  cases it.step using Std.PlausibleIterStep.casesOn with
  | yield it out h =>
    match out with
    | .matched startPos endPos =>
      simp [splitOnLists]
      rw [← ihy h]
    | .rejected startPos endPos =>
      simp [splitOnLists]
      rw [← ihy h]
  | skip it h =>
    simp
    rw [← ihs h]
  | done =>
    simp [splitOnLists]
    have : (Std.Iter.mk (α := SplitIterator pat s) SplitIterator.atEnd).toList = [] := by
      rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
      simp [Std.Iter.toIterM]
    rw [← this]

theorem toList_eq_splitOnLists {ρ : Type} {pat : ρ} {σ : Slice → Type} [ToForwardSearcher pat σ]
    [∀ s, Std.Iterator (σ s) Id (SearchStep s)] [∀ s, Std.Iterators.Finite (σ s) Id] (s : Slice) :
    (s.splitToSubslice pat).toList = splitOnLists s.startPos (ToForwardSearcher.toSearcher pat s).toList := by
  rw [splitToSubslice, toList_eq_splitOnLists']

theorem toList_eq_splitModel {ρ : Type} (pat : ρ) [ForwardPatternModel pat]
    {σ : Slice → Type} [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] [LawfulToForwardSearcherModel pat] (s : Slice) :
    (s.splitToSubslice pat).toList = (splitModel pat s.startPos).l := by
  rw [toList_eq_splitOnLists, IsValidSearchFrom.splitOnLists_eq_splitModel pat _
    s.startPos s.startPos (Std.le_refl _) _ (LawfulToForwardSearcherModel.isValidSearchFrom_toList _),
    SplitFrom.extend_self]
  exact fun p hp₁ hp₂ => False.elim (Std.lt_irrefl (Std.lt_of_le_of_lt hp₁ hp₂))

namespace ForwardSliceSearcher

instance {pat : Slice} : ForwardPatternModel pat where
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

theorem isLongestMatchAt_iff_extract {pat s : Slice} {pos₁ pos₂ : s.Pos} (h : pat.isEmpty = false) :
    IsLongestMatchAt pat pos₁ pos₂ ↔ s.copy.toByteArray.extract pos₁.offset.byteIdx pos₂.offset.byteIdx = pat.copy.toByteArray := by

  have heq (h₁ : pos₁ ≤ pos₂) :
      min (s.startInclusive.offset.byteIdx + pos₂.offset.byteIdx) s.endExclusive.offset.byteIdx =
        s.startInclusive.offset.byteIdx + pos₁.offset.byteIdx + (pos₂.offset.byteIdx - pos₁.offset.byteIdx) := by
    have := pos₂.str_le_endExclusive
    simp only [Pos.le_iff, Pos.Raw.le_iff, String.Pos.le_iff, Pos.offset_str,
      Pos.Raw.byteIdx_offsetBy] at h₁ this
    omega
  refine ⟨fun ⟨h₁, h₂⟩ => ?_, fun h' => ?_⟩
  · rw [isLongestMatch_iff h] at h₂
    rw [← h₂]
    simp [toByteArray_copy, ByteArray.extract_extract, heq h₁]
  · have h₁ : pos₁ ≤ pos₂ := by
      have := congrArg ByteArray.size h'
      simp at this
      simp [isEmpty_eq] at h
      simp [Pos.le_iff, Pos.Raw.le_iff]
      omega
    refine ⟨h₁, ?_⟩
    rw [isLongestMatch_iff h]
    simp [← toByteArray_inj, ← h']
    simp [toByteArray_copy, ByteArray.extract_extract, heq h₁]

theorem size_le_of_matchesAt {pat s : Slice} (hpat : pat.isEmpty = false) {pos : s.Pos} :
    MatchesAt pat pos → pos.offset.byteIdx + pat.copy.toByteArray.size ≤ s.copy.toByteArray.size := by
  rintro ⟨⟨endPos, hend⟩⟩
  rw [isLongestMatchAt_iff_extract hpat] at hend
  have h₁ := congrArg ByteArray.size hend
  have h₂ := pos.str_le_endExclusive
  simp [String.Pos.le_iff, Pos.Raw.le_iff, utf8ByteSize_eq] at ⊢ h₁ h₂
  omega

theorem not_matchesAt_of_getUTF8Byte_ne {pat s : Slice} (hpat : pat.isEmpty = false) {pos : s.Pos} (off : Pos.Raw)
    {hoff₁ hoff₂}
    (h : s.getUTF8Byte (off.offsetBy pos.offset) hoff₁ ≠ pat.getUTF8Byte off hoff₂) :
    ¬ MatchesAt pat pos := by
  rintro ⟨⟨endPos, hend⟩⟩
  rw [isLongestMatchAt_iff_extract hpat] at hend
  have := congrArg (·[off.byteIdx]?) hend
  simp at this
  rw [getElem?_pos, getElem?_pos, Option.some.injEq, ByteArray.getElem_extract] at this
  · simp [getUTF8Byte_eq_getUTF8Byte_copy, String.getUTF8Byte, this] at h
  · simpa [Pos.Raw.lt_iff] using hoff₂
  · simp only [ByteArray.size_extract, size_toByteArray, utf8ByteSize_copy]
    have ht₀ := endPos.isValidForSlice.le_utf8ByteSize
    rw [Nat.min_eq_left (by omega)]
    have : endPos.offset.byteIdx - pos.offset.byteIdx = pat.endExclusive.offset.byteIdx - pat.startInclusive.offset.byteIdx := by
      have := congrArg ByteArray.size hend
      simp only [ByteArray.size_extract, size_toByteArray, utf8ByteSize_copy] at this
      rwa [Nat.min_eq_left (by omega)] at this
    simp [Pos.Raw.lt_iff, utf8ByteSize_eq] at hoff₂
    omega

theorem getElem_eq_of_matchesAt {pat s : Slice} (hpat : pat.isEmpty = false) {pos : s.Pos}
    (h : MatchesAt pat pos) (j : Nat) (hj : j < pat.copy.toByteArray.size) :
    pat.copy.toByteArray[j]'hj = s.copy.toByteArray[pos.offset.byteIdx + j]'(by have := size_le_of_matchesAt hpat h; omega) := by
  rcases h with ⟨⟨endPos, hend⟩⟩
  rw [isLongestMatchAt_iff_extract hpat] at hend
  simp only [← hend]
  simp [ByteArray.getElem_extract]

theorem le_of_matchesAt {pat s : Slice} (hpat : pat.isEmpty = false) {pos : s.Pos}
    (h : MatchesAt pat pos) : pos.offset.byteIdx + pat.utf8ByteSize ≤ s.utf8ByteSize := by
  obtain ⟨⟨endPos, hend⟩⟩ := h
  rw [isLongestMatchAt_iff_extract hpat] at hend
  replace hend := congrArg ByteArray.size hend
  simp [utf8ByteSize_eq] at ⊢ hend
  have := endPos.str_le_endExclusive
  simp [String.Pos.le_iff, Pos.Raw.le_iff] at this
  rw [Nat.min_eq_left (by omega)] at hend
  rw [← hend]
  simp [Slice.isEmpty_eq, utf8ByteSize_eq] at hpat
  omega

theorem startsWith_iff {pat s : Slice} : startsWith pat s ↔ ∃ t, s.copy = pat.copy ++ t := by
  fun_cases startsWith with
  | case1 h hs hp =>
    rw [Internal.memcmpSlice_eq_true_iff]
    refine ⟨fun h => ?_, fun ⟨t, ht⟩ => ?_⟩
    · simp at h
      rw (occs := [2]) [utf8ByteSize_eq_size_toByteArray_copy] at h
      rw [ByteArray.extract_zero_size] at h
      refine ⟨⟨s.copy.toByteArray.extract pat.utf8ByteSize s.utf8ByteSize, ?_⟩, ?_⟩
      · rw [utf8ByteSize_eq_size_toByteArray_copy (s := s)]
        apply Pos.Raw.IsValid.isValidUTF8_extract_utf8ByteSize
        rw [Pos.Raw.isValid_iff_isValidUTF8_extract_zero]
        simp only
        rw [← pat.utf8ByteSize_eq, h]
        exact ⟨by simpa [Pos.Raw.le_iff], pat.copy.isValidUTF8⟩
      · rw [← toByteArray_inj, toByteArray_append]
        simp only [← h]
        rw [ByteArray.extract_append_extract, Nat.min_eq_left (Nat.zero_le _), Nat.max_eq_right ‹_›,
          utf8ByteSize_eq_size_toByteArray_copy, ByteArray.extract_zero_size]
    · simp [ht]
      rw [ByteArray.extract_append_eq_left utf8ByteSize_eq_size_toByteArray_copy,
        utf8ByteSize_eq_size_toByteArray_copy, ByteArray.extract_zero_size]
  | case2 =>
    simp only [Bool.false_eq_true, false_iff, not_exists]
    intro t
    apply ne_of_apply_ne String.utf8ByteSize
    simp [utf8ByteSize_eq] at *
    omega

theorem dropPrefix?_eq_some_iff {pat s : Slice} {pos : s.Pos} :
    dropPrefix? pat s = some pos ↔ (s.sliceTo pos).copy = pat.copy := by
  fun_cases dropPrefix? with
  | case1 h =>
    obtain ⟨t, ht⟩ := startsWith_iff.1 h
    have hval : pat.rawEndPos.IsValidForSlice s := by
      rw [← Pos.Raw.isValid_copy_iff, ht, ← Slice.rawEndPos_copy]
      exact Pos.Raw.isValid_rawEndPos.append_right _
    refine ⟨?_, ?_⟩
    · have hsplit : (s.pos pat.rawEndPos hval).Splits pat.copy t := by
        apply Pos.splits_of_splits_copy
        rw [Slice.copy_pos]
        rw [← String.Pos.splits_cast_iff (h := ht), String.cast_pos]
        simp only [← rawEndPos_copy]
        exact Pos.splits_append_rawEndPos
      simp only [Option.some.injEq]
      rintro rfl
      rw [pos!_eq_pos hval, hsplit.copy_sliceTo_eq]
    · simp only [Option.some.injEq]
      intro heq
      rw [pos!_eq_pos hval]
      simpa [Slice.Pos.ext_iff, Pos.Raw.ext_iff, utf8ByteSize_eq] using (congrArg String.utf8ByteSize heq).symm
  | case2 h =>
    simp only [startsWith_iff, not_exists] at h
    simp only [reduceCtorEq, false_iff]
    intro heq
    have := h (s.sliceFrom pos).copy
    simp [← heq, pos.splits.eq_append] at this

theorem isSome_dropPrefix? {pat s : Slice} : (dropPrefix? pat s).isSome = startsWith pat s := by
  fun_cases dropPrefix? <;> simp_all

theorem lawfulForwardPatternModel {pat : Slice} (hpat : pat.isEmpty = false) :
    LawfulForwardPatternModel pat where
  dropPrefixOfNonempty?_eq h := rfl
  startsWith_eq s := isSome_dropPrefix?.symm
  dropPrefix?_eq_some_iff s := by
    simp [ForwardPattern.dropPrefix?, dropPrefix?_eq_some_iff, isLongestMatch_iff hpat]

structure PrefixProperty (b : ByteArray) (i : Nat) (hi : i < b.size) (k : Nat) : Prop where
  le : k ≤ i
  getElem_eq (j) (hj : j < k) : b[j] = b[i - k + 1 + j]

theorem prefixProperty_iff {b : ByteArray} {i : Nat} {hi} {k : Nat} :
    PrefixProperty b i hi k ↔ ∃ (h : k ≤ i), ∀ (j : Nat) (hj : j < k), b[j] = b[i - k + 1 + j] :=
  ⟨fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem prefixProperty_add_one_add_one_iff {b : ByteArray} (i : Nat)
    (hi : i + 1 < b.size) (k : Nat) :
    PrefixProperty b (i + 1) hi (k + 1) ↔
      ∃ (h : PrefixProperty b i (by omega) k), b[k]'(have := h.le; by omega) = b[i + 1] := by
  refine ⟨fun ⟨hle, h⟩ => ?_, fun ⟨⟨hle, h⟩, h'⟩ => ?_⟩
  · exact ⟨⟨by omega, fun j hj => by simp [h j (by omega)]; congr 1; omega⟩, by simp [h k (by omega)]; congr 1; omega⟩
  · refine ⟨by omega, fun j hj => ?_⟩
    by_cases hjk : j < k
    · simp [h j hjk]
      congr 1
      omega
    · obtain rfl : j = k := by omega
      simp [h']
      congr 1
      omega

theorem prefixProperty_iff_of_prefixProperty {b : ByteArray} {i : Nat} {hi : i < b.size} {k : Nat}
    (h₀ : PrefixProperty b i hi k) {k' : Nat} :
    PrefixProperty b (k - 1) (have := h₀.le; by omega) k' ↔ k' ≤ k - 1 ∧ PrefixProperty b i hi k' := by
  have := h₀.le
  refine ⟨fun ⟨hle, h⟩ => ⟨hle, ?_⟩, fun ⟨hk', ⟨hle, h⟩⟩ => ?_⟩
  · refine ⟨by omega, fun j hj => ?_⟩
    rw [h j hj, h₀.getElem_eq _ (by omega)]
    congr 1
    omega
  · refine ⟨hk', fun j hj => ?_⟩
    rw [h j hj]
    conv => rhs; rw [h₀.getElem_eq _ (by omega)]
    congr 1
    omega

instance {b i hi k} : Decidable (PrefixProperty b i hi k) :=
  decidable_of_iff' _ prefixProperty_iff

@[simp]
theorem prefixProperty_zero {b : ByteArray} {i : Nat} {hi} : PrefixProperty b i hi 0 where
  le := by simp
  getElem_eq := by simp

def prefixFunction (b : ByteArray) (i : Nat) (hi : i < b.size) : Nat :=
  go i
where go (k : Nat) : Nat :=
  if h : PrefixProperty b i hi k then
    k
  else
    have : 0 < k := Nat.pos_iff_ne_zero.2 (by rintro rfl; simp_all)
    go (k - 1)

theorem prefixFunction_eq_iff {b i hi k} :
    prefixFunction b i hi = k ↔ PrefixProperty b i hi k ∧ ∀ k', k < k' → ¬ PrefixProperty b i hi k' := by
  rw [prefixFunction]
  suffices ∀ k₀,
      (∀ k', k₀ < k' → ¬ PrefixProperty b i hi k') →
      ∀ k, prefixFunction.go b i hi k₀ = k ↔ PrefixProperty b i hi k ∧ (∀ k', k < k' → ¬ PrefixProperty b i hi k') from
    this _ (fun k' hk' hp => Nat.lt_irrefl _ (Nat.lt_of_le_of_lt hp.le hk')) ..
  intro k₀ hk₀ k
  fun_induction prefixFunction.go with
  | case1 k' hk' =>
    refine ⟨?_, ?_⟩
    · rintro rfl
      exact ⟨hk', hk₀⟩
    · rintro ⟨h₁, h₂⟩
      refine Nat.le_antisymm ?_ ?_ <;> exact Nat.not_lt.1 (fun hkk' => by simp_all)
  | case2 k' hk' h₀ ih =>
    rw [ih]
    intro k₀ hk₀'
    by_cases hk'k₀ : k' < k₀
    · exact hk₀ _ hk'k₀
    · obtain rfl : k' = k₀ := by omega
      exact hk'

theorem PrefixProperty.le_prefixFunction {b i hi k} (h : PrefixProperty b i hi k) :
    k ≤ prefixFunction b i hi :=
  Nat.not_lt.1 (fun hx => (prefixFunction_eq_iff.1 rfl).2 _ hx h)

theorem prefixProperty_prefixFunction {b i hi} : PrefixProperty b i hi (prefixFunction b i hi) :=
  ((prefixFunction_eq_iff).1 rfl).1

theorem prefixFunction_le {b i hi} : prefixFunction b i hi ≤ i :=
  prefixProperty_prefixFunction.le

@[simp]
theorem prefixFunction_zero {b hi} : prefixFunction b 0 hi = 0 :=
  Nat.le_zero.1 prefixFunction_le

theorem le_prefixFunction_of_prefixProperty {b i hi} {k k' : Nat} (h : k' < k)
    (h₁ : PrefixProperty b i hi k) (h₂ : PrefixProperty b i hi k') :
    k' ≤ prefixFunction b (k - 1) (by have := h₁.le; omega) :=
  ((prefixProperty_iff_of_prefixProperty h₁).2 ⟨by omega, h₂⟩).le_prefixFunction

structure IsComputeDistance (b : ByteArray) (i : Nat) (hi : i + 1 < b.size) (k : Nat) where
  prefixProperty : PrefixProperty b i (by omega) k
  not_or_ne (k') (hk' : k < k') (h₀ : k' < b.size) :
    ¬ PrefixProperty b i (by omega) k' ∨ b[i + 1] ≠ b[k']
  eq_zero_or : k = 0 ∨ b[i + 1] = b[k]'(have := prefixProperty.le; by omega)

theorem IsComputeDistance.prefixFunction_eq {b : ByteArray} {i : Nat} {hi : i + 1 < b.size} {k : Nat}
    (h : IsComputeDistance b i hi k) :
    prefixFunction b (i + 1) (by omega) =
      if b[i + 1] = b[k]'(have := h.prefixProperty.le; by omega) then k + 1 else k := by
  split <;> rename_i h₁
  · rw [prefixFunction_eq_iff, prefixProperty_add_one_add_one_iff]
    refine ⟨⟨h.prefixProperty, h₁.symm⟩, fun k' hk' => ?_⟩
    have : k' = k' - 1 + 1 := by omega
    rw [this, prefixProperty_add_one_add_one_iff]
    simp only [not_exists]
    intro h''
    have := h''.le
    have := h.not_or_ne (k' - 1) (by omega) (by omega)
    simp only [h'', not_true_eq_false, ne_eq, false_or] at this
    exact Ne.symm this
  · obtain rfl : k = 0 := by
      obtain (h|h) := h.eq_zero_or
      · assumption
      · simp [h] at h₁
    rw [prefixFunction_eq_iff]
    refine ⟨by simp, fun k' hk' hcontr => ?_⟩
    have : k' = k' - 1 + 1 := by omega
    have hcle := hcontr.le
    rw [this, prefixProperty_add_one_add_one_iff] at hcontr
    obtain ⟨hc₁, hc₂⟩ := hcontr
    by_cases hkk' : k' = 1
    · cases hkk'
      simp [hc₂] at h₁
    · obtain (hcc|hcc) := h.not_or_ne (k' - 1) (by omega) (by omega)
      · contradiction
      · simp [hc₂] at hcc

structure IsTable (b : ByteArray) (v : Array Nat) : Prop where
  size_le : v.size ≤ b.size
  eq_prefixFunction (i : Nat) (hi) : v[i]'hi = prefixFunction b i (by omega)

theorem isTable_empty : IsTable ByteArray.empty #[] where
  size_le := by simp
  eq_prefixFunction := by simp

theorem isTable_singleton {b : ByteArray} (hb : 1 ≤ b.size) : IsTable b #[0] where
  size_le := by simp [hb]
  eq_prefixFunction := by simp +contextual

theorem IsTable.push {b : ByteArray} {v : Array Nat} (h : IsTable b v) {d : Nat}
    (hle : v.size + 1 ≤ b.size)
    (hd : d = prefixFunction b v.size (by omega)) :
    IsTable b (v.push d) where
  size_le := by simpa using hle
  eq_prefixFunction i hi := by
    rw [Array.getElem_push]
    split <;> rename_i hi'
    · rw [h.eq_prefixFunction]
    · rw [Array.size_push] at hi
      obtain rfl : i = v.size := by omega
      exact hd

private theorem computeDistance_correct {s : Slice} (i : Nat) (hi : i + 1 < s.copy.toByteArray.size) {patByte : UInt8}
    (hpat : patByte = s.copy.toByteArray[i + 1])
    (table : Array Nat) {ht} (ht' : IsTable s.copy.toByteArray table)
    {h guess hg} (hg' : PrefixProperty s.copy.toByteArray i (by omega) guess) (ih : ∀ g', guess < g' → (hg' : g' < s.copy.toByteArray.size) →
      ¬ PrefixProperty s.copy.toByteArray i (by omega) g' ∨ s.copy.toByteArray[i + 1] ≠ s.copy.toByteArray[g']) :
    IsComputeDistance s.copy.toByteArray i hi
    (buildTable.computeDistance s patByte table ht h guess hg).1 := by
  fun_induction buildTable.computeDistance with
  | case1 g hg hif =>
    refine ⟨hg', ih, ?_⟩
    simp [hpat, getUTF8Byte_eq_getUTF8Byte_copy, String.getUTF8Byte] at ⊢ hif
    rw [eq_comm (a := s.copy.toByteArray[i + 1])]
    exact hif
  | case2 g hg hif htab ih₀ =>
    apply ih₀
    · rw [ht'.eq_prefixFunction]
      rw [utf8ByteSize_eq_size_toByteArray_copy] at ht
      have := prefixProperty_prefixFunction (b := s.copy.toByteArray) (i := g - 1) (hi := by omega)
      rw [prefixProperty_iff_of_prefixProperty hg'] at this
      exact this.2
    · intro g' hg₀ hg'₀
      by_cases hgg' : g < g'
      · apply ih _ hgg'
      · by_cases hgg₂ : g' < g
        · refine Or.inl (fun hpp => ?_)
          rw [ht'.eq_prefixFunction] at hg₀
          have := le_prefixFunction_of_prefixProperty hgg₂ hg' hpp
          omega
        · obtain rfl : g = g' := by omega
          refine Or.inr ?_
          simp [hpat, getUTF8Byte_eq_getUTF8Byte_copy, String.getUTF8Byte] at hif
          exact Ne.symm hif.2

private theorem isTable_buildTableGo {s : Slice} {table : Array Nat} {ht₀ ht h}
    (htab : IsTable s.copy.toByteArray table) :
    IsTable s.copy.toByteArray (buildTable.go s table ht₀ ht h).toArray := by
  fun_induction buildTable.go with
  | case1 table ht₀ ht h h' patByte dist dist' ih =>
    rw [utf8ByteSize_eq_size_toByteArray_copy] at h'
    apply ih
    apply htab.push (by omega)
    have : IsComputeDistance s.copy.toByteArray (table.size - 1) (by omega) dist.1 := by
      simp only [dist]
      apply computeDistance_correct
      · simp [patByte, (by omega : table.size - 1 + 1 = table.size),
          getUTF8Byte_eq_getUTF8Byte_copy, String.getUTF8Byte]
      · exact htab
      · rw [htab.eq_prefixFunction]
        exact prefixProperty_prefixFunction
      · intro g' hg' hg''
        rw [htab.eq_prefixFunction] at hg'
        refine Or.inl (fun hcontr => ?_)
        have := hcontr.le_prefixFunction
        omega
    have := this.prefixFunction_eq
    simp only [dist']
    simp [(by omega : table.size - 1 + 1 = table.size)] at this
    simp [this, patByte, getUTF8Byte_eq_getUTF8Byte_copy,
      String.getUTF8Byte]
    simp only [eq_comm (a := s.copy.toByteArray[table.size])]
  | case2 table ht₀ ht h h' => simpa

theorem isTable_buildTable {s : Slice} : IsTable s.copy.toByteArray (buildTable s).toArray := by
  fun_cases buildTable with
  | case1 h =>
    simpa [(Slice.copy_eq_empty_iff (s := s)).2 (by simp [Slice.isEmpty_eq, h])] using isTable_empty
  | case2 h arr arr' =>
    apply isTable_buildTableGo
    simp [arr, arr']
    apply isTable_singleton
    simp [utf8ByteSize_eq] at ⊢ h
    omega

structure PartialMatch (pat s : ByteArray) (stackPos : Nat) (needlePos : Nat) : Prop where
  hi : stackPos ≤ s.size
  le : needlePos ≤ stackPos
  le_size : needlePos ≤ pat.size
  getElem_eq (j) (jh : j < needlePos) : pat[j] = s[stackPos - needlePos + j]

theorem PartialMatch.zero {pat s : ByteArray} {stackPos : Nat} (h : stackPos ≤ s.size) :
    PartialMatch pat s stackPos 0 where
  hi := h
  le := by simp
  le_size := by simp
  getElem_eq := by simp

theorem PartialMatch.inc {pat s : ByteArray} {stackPos needlePos : Nat} (h₀ : PartialMatch pat s stackPos needlePos)
    (h₁ : needlePos < pat.size) (h₂ : stackPos < s.size)
    (h : pat[needlePos] = s[stackPos]) : PartialMatch pat s (stackPos + 1) (needlePos + 1) where
  hi := by omega
  le := by simp [h₀.le]
  le_size := by omega
  getElem_eq j hj := by
    by_cases hj' : j < needlePos
    · simp [h₀.getElem_eq j hj']
      congr 1
      omega
    · obtain rfl : needlePos = j := by omega
      simp [h]
      have := h₀.le
      congr 1
      omega

theorem PartialMatch.extract_eq {pat s : ByteArray} {stackPos : Nat} {needlePos : Nat} (h : PartialMatch pat s stackPos needlePos) :
    s.extract (stackPos - needlePos) stackPos = pat.extract 0 needlePos := by
  apply ByteArray.ext_getElem
  · simp [h.le_size, h.hi]
    have := h.le
    omega
  · intro i hi hi'
    simp [ByteArray.getElem_extract, h.getElem_eq i (by simp_all; omega)]

theorem PartialMatch.extract_eq_all {pat s : ByteArray} {stackPos needlePos : Nat} (h : PartialMatch pat s stackPos needlePos) (h' : needlePos = pat.size) :
    s.extract (stackPos - needlePos) stackPos = pat := by
  rw [h.extract_eq, h', ByteArray.extract_zero_size]

theorem PartialMatch.partialMatch_of_prefixFunction_eq {pat s : ByteArray} {stackPos needlePos : Nat}
    (h : PartialMatch pat s stackPos needlePos) (h' : 0 < needlePos) {k : Nat} {hki} (hk : prefixFunction pat (needlePos - 1) hki = k) :
    PartialMatch pat s stackPos k := by
  cases hk
  obtain ⟨h₁, h₂⟩ := prefixProperty_prefixFunction (hi := hki)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h.hi
  · have := h.le
    omega
  · omega
  · intro j hj
    have := h.getElem_eq
    have : stackPos - prefixFunction pat (needlePos - 1) hki + j =
        stackPos - needlePos + (needlePos - 1 - prefixFunction pat (needlePos - 1) hki + 1 + j) := by
      have := h.le
      omega
    simp only [this]
    rw [← h.getElem_eq]
    · rw [h₂ _ hj]
    · omega

-- theorem PartialMatch.not_matchesAt_of_prefixFunction_eq {pat s : ByteArray} {stackPos needlePos : Nat}
--     (h : PartialMatch pat s stackPos needlePos) (h' : 0 < needlePos) {h : Nat} {hki} (hk : prefixFunction pat (needlePos - 1) hki = k) :
--     False := sorry

structure Invariants (pat s : Slice) (stackPos needlePos : String.Pos.Raw) : Prop where
  isEmpty_eq_false : pat.isEmpty = false
  partialMatch : PartialMatch pat.copy.toByteArray s.copy.toByteArray stackPos.byteIdx needlePos.byteIdx
  isValid : (stackPos.unoffsetBy needlePos).IsValidForSlice s

theorem Invariants.start (pat s : Slice) (h : pat.isEmpty = false) : Invariants pat s s.startPos.offset pat.startPos.offset where
  isEmpty_eq_false := h
  partialMatch := .zero (by simp)
  isValid := by simp [Pos.Raw.unoffsetBy]

theorem Invariants.offset {pat s : Slice} (h : pat.isEmpty = false) (p : s.Pos) : Invariants pat s p.offset pat.startPos.offset where
  isEmpty_eq_false := h
  partialMatch := .zero
    (by rw [← utf8ByteSize_eq_size_toByteArray_copy, ← byteIdx_rawEndPos, ← Pos.Raw.le_iff]; simp)
  isValid := by simp

theorem Invariants.inc {pat s : Slice} {stackPos needlePos : String.Pos.Raw} (h₀ : Invariants pat s stackPos needlePos)
    (h₁ h₂)
    (h : pat.getUTF8Byte needlePos h₁ = s.getUTF8Byte stackPos h₂) : Invariants pat s stackPos.inc needlePos.inc where
  isEmpty_eq_false := h₀.isEmpty_eq_false
  partialMatch := h₀.partialMatch.inc (by simpa using h₁) (by simpa using h₂) (by simpa [getUTF8Byte_eq_getUTF8Byte_copy] using h)
  isValid := by simpa using h₀.isValid

theorem Invariants.of_prefixFunction_eq {pat s : Slice} {stackPos needlePos : String.Pos.Raw} (hst : stackPos < s.rawEndPos) (h : Invariants pat s stackPos needlePos)
    (h' : 0 < needlePos) {k : Nat} {hki} (hk : prefixFunction pat.copy.toByteArray (needlePos.byteIdx - 1) hki = k) (hk₀ : 0 < k) :
    Invariants pat s stackPos ⟨k⟩ := by
  refine ⟨h.isEmpty_eq_false, h.partialMatch.partialMatch_of_prefixFunction_eq h' hk, ?_⟩
  rw [Pos.Raw.isValidForSlice_iff_isUTF8FirstByte]
  refine Or.inr ⟨?_, ?_⟩
  · simp [Pos.Raw.lt_iff] at ⊢ hst
    omega
  · have := (h.partialMatch.partialMatch_of_prefixFunction_eq h' hk).getElem_eq 0 hk₀
    simp at this
    rw [getUTF8Byte_eq_getUTF8Byte_copy, String.getUTF8Byte]
    simp
    rw [← this]
    exact isUTF8FirstByte_getUTF8Byte_zero

theorem Invariants.prefixProperty_of_matchesAt {pat s : Slice} {stackPos needlePos : String.Pos.Raw}
    (h : Invariants pat s stackPos needlePos) (h' : 0 < needlePos.byteIdx) (pos : s.Pos)
    (hp' : stackPos.byteIdx - pos.offset.byteIdx ≤ needlePos.byteIdx - 1)
    (hm : MatchesAt pat pos) :
    PrefixProperty pat.copy.toByteArray
      (needlePos.byteIdx - 1) (by have := h.partialMatch.le_size; omega) (stackPos.byteIdx - pos.offset.byteIdx) :=by
  refine ⟨by omega, fun j hj => ?_⟩
  have := h.partialMatch.getElem_eq
  rw [getElem_eq_of_matchesAt h.isEmpty_eq_false hm, this]
  · congr 1
    have := h.partialMatch.le
    omega
  · omega

theorem Invariants.not_matchesAt_of_prefixFunction_eq {pat s : Slice} {stackPos needlePos : String.Pos.Raw}
    (h : Invariants pat s stackPos needlePos)
    (h' : 0 < needlePos) {k : Nat} {hki} (hk : prefixFunction pat.copy.toByteArray (needlePos.byteIdx - 1) hki = k)
    (p : s.Pos) (hp₁ : stackPos.unoffsetBy needlePos ≤ p.offset) (hp₂ : p.offset < stackPos.unoffsetBy ⟨k⟩)
    {h₁ h₂}
    (hmism : s.getUTF8Byte stackPos h₁ ≠ pat.getUTF8Byte needlePos h₂) :
    ¬ MatchesAt pat p := by
  by_cases hcas : stackPos.byteIdx - p.offset.byteIdx ≤ needlePos.byteIdx - 1
  · intro hcontr
    have := h.prefixProperty_of_matchesAt h' _ hcas hcontr
    have := this.le_prefixFunction
    rw [hk] at this
    simp [Pos.Raw.lt_iff] at hp₂
    omega
  · obtain rfl : stackPos = needlePos.offsetBy p.offset := by
      simp [Pos.Raw.le_iff, Pos.Raw.ext_iff] at hp₁ ⊢
      omega
    exact not_matchesAt_of_getUTF8Byte_ne h.isEmpty_eq_false _ hmism

section

variable {pat s : Slice} {stackPos needlePos : String.Pos.Raw}

theorem Invariants.extract_eq (h : Invariants pat s stackPos needlePos) :
    s.copy.toByteArray.extract (stackPos.unoffsetBy needlePos).byteIdx stackPos.byteIdx = pat.copy.toByteArray.extract 0 needlePos.byteIdx :=
  h.partialMatch.extract_eq

theorem Invariants.extract_eq_all (h : Invariants pat s stackPos needlePos) (h' : needlePos = pat.rawEndPos) :
    s.copy.toByteArray.extract (stackPos.unoffsetBy needlePos).byteIdx stackPos.byteIdx = pat.copy.toByteArray :=
  h.partialMatch.extract_eq_all (by simpa [Pos.Raw.ext_iff] using h')

theorem Invariants.isValidUTF8 (h : Invariants pat s stackPos needlePos) (h' : needlePos = pat.rawEndPos) :
    (s.copy.toByteArray.extract (stackPos.unoffsetBy needlePos).byteIdx stackPos.byteIdx).IsValidUTF8 := by
  rw [h.extract_eq_all h']
  exact pat.copy.isValidUTF8

theorem Invariants.stackPos_le_rawEndPos (h : Invariants pat s stackPos needlePos) :
    stackPos ≤ s.rawEndPos := by
  simpa [Pos.Raw.le_iff] using h.partialMatch.hi

theorem Invariants.isValidForSlice_stackPos (h : Invariants pat s stackPos needlePos) (h' : needlePos = pat.rawEndPos) :
    stackPos.IsValidForSlice s := by
  obtain (hx|hx) := (Pos.Raw.isValidUTF8_extract_iff _ _ (by simp) (by simpa using h.stackPos_le_rawEndPos)).1 (h.isValidUTF8 h')
  · rw [← hx]
    exact h.isValid
  · exact Pos.Raw.isValid_copy_iff.1 hx.2

theorem Invariants.isValidForSlice_stackPos_zero (h : Invariants pat s stackPos needlePos) (h' : needlePos.byteIdx = 0) :
    stackPos.IsValidForSlice s := by
  suffices stackPos.unoffsetBy needlePos = stackPos by simpa [this] using h.isValid
  simp [Pos.Raw.ext_iff, h']

def Invariants.base (h : Invariants pat s stackPos needlePos) : s.Pos :=
  s.pos _ h.isValid

def Invariants.stackValidPos (h : Invariants pat s stackPos needlePos) (h' : needlePos = pat.rawEndPos) : s.Pos :=
  s.pos _ (h.isValidForSlice_stackPos h')

theorem Invariants.isLongestMatchAt (h : Invariants pat s stackPos needlePos) (h' : needlePos = pat.rawEndPos) :
    IsLongestMatchAt pat h.base (h.stackValidPos h') := by
  rw [isLongestMatchAt_iff_extract h.isEmpty_eq_false, ← h.extract_eq_all h']
  simp [base, stackValidPos]

end


theorem Invariants.base_start {pat s : Slice} (h : pat.isEmpty = false) : (Invariants.start pat s h).base = s.startPos :=
  (rfl)

theorem Invariants.isValidSearchFrom_toList {pat s : Slice} {stackPos needlePos : String.Pos.Raw}
    (hpat : pat.isEmpty = false)
    (it : Std.Iter (α := ForwardSliceSearcher s) (SearchStep s))
    (h : Invariants pat s stackPos needlePos)
    {table ht hn}
    (heq : it = Std.Iter.mk (.proper pat table ht stackPos needlePos hn)) {p : s.Pos} (hp : p = h.base) :
    IsValidSearchFrom pat p it.toList := by
  induction it using Std.Iter.inductSteps generalizing p stackPos needlePos with | step it ihy ihs
  cases heq
  cases hp
  rw [Std.Iter.toList_eq_match_step]
  generalize hit' : (Std.Iter.mk (α := ForwardSliceSearcher s) (.proper pat table ht stackPos needlePos hn)).step = it'

  have hit'' := congrArg Subtype.val hit'
  have plausible := it'.property
  simp only [Std.Iter.step_eq, ne_eq, Std.Iter.toIterM] at hit''
  split at hit'' <;> rename_i h₁
  · split at hit'' <;> rename_i h₂
    · split at hit'' <;> rename_i h₃
      · have hinc := h.inc _ _ h₂.symm
        simp only [Id.run_pure, Std.Shrink.inflate_deflate,
          Std.IterM.Step.toPure_yield, Std.PlausibleIterStep.yield] at hit''
        rw [s.pos!_eq_pos hinc.isValid, s.pos!_eq_pos (hinc.isValidForSlice_stackPos h₃)] at hit''
        simp [← hit''] at ⊢ plausible
        apply IsValidSearchFrom.matched_of_eq
        · apply ihy plausible _ rfl rfl
          exact ⟨hpat, .zero (by simpa [Pos.Raw.le_iff, Pos.Raw.lt_iff]),
            by simpa using hinc.isValidForSlice_stackPos h₃⟩
        · simpa [Invariants.base] using hinc.isLongestMatchAt h₃
        · simp [Invariants.base]
      · have hinc := h.inc _ _ h₂.symm
        simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_skip,
          Std.PlausibleIterStep.skip] at hit''
        simp [← hit''] at ⊢ plausible
        exact ihs plausible hinc rfl (by simp [Invariants.base])
    · split at hit'' <;> rename_i h₃
      · simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield] at hit''
        obtain rfl : needlePos = 0 := by simpa [Pos.Raw.ext_iff]
        rw [pos!_eq_pos (h.isValidForSlice_stackPos_zero h₃)] at hit''
        simp [← hit''] at ⊢ plausible
        apply IsValidSearchFrom.mismatched_of_eq
        · exact ihy plausible (.offset hpat _) rfl rfl
        · simp only [base, Pos.lt_iff, offset_pos]
          exact Pos.Raw.lt_of_le_of_lt Pos.Raw.unoffsetBy_le_self lt_offset_posGT
        · intro p hp₁ hp₂
          simp [base] at hp₁
          rw [posGT_eq_next (h.isValidForSlice_stackPos_zero h₃),
            Pos.lt_next_iff_le] at hp₂
          obtain rfl : p = s.pos stackPos (h.isValidForSlice_stackPos_zero h₃) :=
            Std.le_antisymm hp₂ hp₁
          exact not_matchesAt_of_getUTF8Byte_ne hpat 0 h₂
        · simp [base]
      · simp [Pos.Raw.lt_iff] at hn
        have hxx : needlePos.byteIdx - 1 < pat.utf8ByteSize := by omega
        have hxx' : needlePos.byteIdx - 1 < pat.copy.toByteArray.size := by
          rw [← utf8ByteSize_eq_size_toByteArray_copy]; omega
        have htt : table[needlePos.byteIdx - 1] = prefixFunction pat.copy.toByteArray (needlePos.byteIdx - 1) hxx' := by
          cases ht
          rw [← Vector.getElem_toArray, isTable_buildTable.eq_prefixFunction]
          simpa
        split at hit'' <;> rename_i h₄
        · simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
            Std.PlausibleIterStep.yield] at hit''
          rw [pos!_eq_pos h.isValid] at hit''
          simp [← hit''] at ⊢ plausible
          apply IsValidSearchFrom.mismatched_of_eq
          · exact ihy plausible (.offset hpat _) rfl rfl
          · simp [base]
            have := h.partialMatch.le
            simp [Pos.Raw.lt_iff]
            omega
          · intro p hp₁ hp₂
            simp [base, Pos.le_iff] at hp₁
            rw [lt_posGE_iff] at hp₂
            exact h.not_matchesAt_of_prefixFunction_eq (by simp [Pos.Raw.lt_iff]; omega) htt.symm
              _ hp₁ (by simpa [h₄]) h₂
          · simp [base]
        · simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
            Std.PlausibleIterStep.yield] at hit''
          have hinv := h.of_prefixFunction_eq h₁ (by simp [Pos.Raw.lt_iff]; omega) htt.symm (by omega)
          rw [pos!_eq_pos h.isValid, pos!_eq_pos hinv.isValid] at hit''
          simp [← hit''] at ⊢ plausible
          apply IsValidSearchFrom.mismatched_of_eq
          · exact ihy plausible hinv rfl rfl
          · simp [base, Pos.lt_iff, Pos.Raw.lt_iff]
            have := h.partialMatch.le
            suffices table[needlePos.byteIdx - 1] < needlePos.byteIdx by omega
            rw [htt]
            refine Std.lt_of_le_of_lt (prefixProperty_prefixFunction).le (by omega)
          · intro p hp₁ hp₂
            simp [base, Pos.le_iff] at hp₁
            simp [Pos.lt_iff] at hp₂
            exact h.not_matchesAt_of_prefixFunction_eq (by simp [Pos.Raw.lt_iff]; omega) htt.symm
              _ hp₁ hp₂ h₂
          · simp [base]
  · obtain rfl : stackPos = s.rawEndPos := by
      have := h.partialMatch.hi
      rw [← utf8ByteSize_eq_size_toByteArray_copy, ← byteIdx_rawEndPos, ← Pos.Raw.le_iff] at this
      rw [Std.not_lt] at h₁
      exact Std.le_antisymm this h₁
    split at hit'' <;> rename_i h₂
    · simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
        Std.PlausibleIterStep.yield] at hit''
      rw [pos!_eq_pos h.isValid] at hit''
      simp [← hit''] at ⊢ plausible
      apply IsValidSearchFrom.mismatched_of_eq
      · rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
        simpa [Std.Iter.toIterM] using IsValidSearchFrom.endPos
      · have := h.partialMatch.le
        have := h.partialMatch.hi
        rw [← utf8ByteSize_eq_size_toByteArray_copy] at this
        simp [base, Pos.lt_iff, Pos.Raw.lt_iff] at ⊢ h₁ h₂
        omega
      · intro pos hp₁ hp₂ hcontr
        have := le_of_matchesAt hpat hcontr
        have := h.partialMatch.le_size
        rw [← utf8ByteSize_eq_size_toByteArray_copy] at this
        simp [base, Pos.Raw.le_iff, Pos.le_iff, Pos.Raw.lt_iff] at hp₁ h₂ hn
        omega
      · simp [base]
    · obtain rfl : needlePos = 0 := by
        simpa [Pos.Raw.ext_iff, Pos.Raw.lt_iff] using h₂
      simpa [← hit'', base] using IsValidSearchFrom.endPos


theorem lawfulToForwardSearcherModel {pat : Slice} (hpat : pat.isEmpty = false) :
    LawfulToForwardSearcherModel pat where
  isValidSearchFrom_toList s := by
    simp only [ToForwardSearcher.toSearcher]
    rw [iter, dif_neg (by simpa [isEmpty_eq] using hpat)]
    rw (occs := [1]) [← Invariants.base_start hpat]
    apply Invariants.isValidSearchFrom_toList hpat _ _ rfl rfl

end ForwardSliceSearcher

end Pattern

end String.Slice
