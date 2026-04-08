/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Char
public import Init.Data.String.Lemmas.Pattern.Basic
public import Init.Data.String.Slice
public import Init.Data.String.Lemmas.Pattern.Pred
public import Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Pattern.Char
import all Init.Data.String.Search
import Init.Data.Option.Lemmas
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Order
import Init.Data.Order.Lemmas
import Init.Data.String.OrderInstances
import Init.Omega
import Init.Data.String.Lemmas.FindPos

public section

namespace String.Slice.Pattern.Model.Char

instance {c : Char} : PatternModel c where
  Matches s := s = String.singleton c

instance {c : Char} : StrictPatternModel c where
  not_matches_empty := by simp [PatternModel.Matches]

instance {c : Char} : NoPrefixPatternModel c :=
  .of_length_eq (by simp +contextual [PatternModel.Matches])

instance {c : Char} : NoSuffixPatternModel c :=
  .of_length_eq (by simp +contextual [PatternModel.Matches])

theorem isMatch_iff {c : Char} {s : Slice} {pos : s.Pos} :
    IsMatch c pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ s.startPos.get h = c := by
  simp only [Model.isMatch_iff, PatternModel.Matches, copy_sliceTo_eq_iff_exists_splits]
  refine ⟨?_, ?_⟩
  · simp only [splits_singleton_iff]
    exact fun ⟨t₂, h, h₁, h₂, h₃⟩ => ⟨h, h₁, h₂⟩
  · rintro ⟨h, rfl, rfl⟩
    exact ⟨_, Slice.splits_next_startPos⟩

theorem isRevMatch_iff {c : Char} {s : Slice} {pos : s.Pos} :
    IsRevMatch c pos ↔
      ∃ (h : s.endPos ≠ s.startPos), pos = s.endPos.prev h ∧ (s.endPos.prev h).get (by simp) = c := by
  simp only [Model.isRevMatch_iff, PatternModel.Matches, copy_sliceFrom_eq_iff_exists_splits]
  refine ⟨?_, ?_⟩
  · simp only [splits_singleton_right_iff]
    exact fun ⟨t₂, h, h₁, h₂, h₃⟩ => ⟨h, h₁, h₂⟩
  · rintro ⟨h, rfl, rfl⟩
    exact ⟨_, Slice.splits_prev_endPos⟩

theorem isLongestMatch_iff {c : Char} {s : Slice} {pos : s.Pos} :
    IsLongestMatch c pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ s.startPos.get h = c := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestMatchAt_iff {c : Char} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAt c pos pos' ↔ ∃ h, pos' = pos.next h ∧ pos.get h = c := by
  simp +contextual [Model.isLongestMatchAt_iff, isLongestMatch_iff, ← Pos.ofSliceFrom_inj,
    Pos.get_eq_get_ofSliceFrom, Pos.ofSliceFrom_next]

theorem isLongestRevMatch_iff {c : Char} {s : Slice} {pos : s.Pos} :
    IsLongestRevMatch c pos ↔
      ∃ (h : s.endPos ≠ s.startPos), pos = s.endPos.prev h ∧ (s.endPos.prev h).get (by simp) = c := by
  rw [isLongestRevMatch_iff_isRevMatch, isRevMatch_iff]

theorem isLongestRevMatchAt_iff {c : Char} {s : Slice} {pos pos' : s.Pos} :
    IsLongestRevMatchAt c pos pos' ↔ ∃ h, pos = pos'.prev h ∧ (pos'.prev h).get (by simp) = c := by
  simp +contextual [Model.isLongestRevMatchAt_iff, isLongestRevMatch_iff, ← Pos.ofSliceTo_inj,
    Pos.get_eq_get_ofSliceTo, Pos.ofSliceTo_prev]

theorem isLongestMatchAt_of_get_eq {c : Char} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : pos.get h = c) : IsLongestMatchAt c pos (pos.next h) :=
  isLongestMatchAt_iff.2 ⟨h, by simp [hc]⟩

theorem isLongestRevMatchAt_of_get_eq {c : Char} {s : Slice} {pos : s.Pos} {h : pos ≠ s.startPos}
    (hc : (pos.prev h).get (by simp) = c) : IsLongestRevMatchAt c (pos.prev h) pos :=
  isLongestRevMatchAt_iff.2 ⟨h, by simp [hc]⟩

instance {c : Char} : LawfulForwardPatternModel c where
  skipPrefix?_eq_some_iff {s} pos := by
    simp [isLongestMatch_iff, ForwardPattern.skipPrefix?, and_comm, eq_comm (b := pos)]

instance {c : Char} : LawfulBackwardPatternModel c where
  skipSuffix?_eq_some_iff {s} pos := by
    simp [isLongestRevMatch_iff, BackwardPattern.skipSuffix?, and_comm, eq_comm (b := pos)]

theorem toSearcher_eq {c : Char} {s : Slice} :
  ToForwardSearcher.toSearcher c s = ToForwardSearcher.toSearcher (· == c) s := (rfl)

theorem toBackwardSearcher_eq {c : Char} {s : Slice} :
  ToBackwardSearcher.toSearcher c s = ToBackwardSearcher.toSearcher (· == c) s := (rfl)

theorem matchesAt_iff {c : Char} {s : Slice} {pos : s.Pos} :
    MatchesAt c pos ↔ ∃ (h : pos ≠ s.endPos), pos.get h = c := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff, exists_comm]

theorem revMatchesAt_iff {c : Char} {s : Slice} {pos : s.Pos} :
    RevMatchesAt c pos ↔ ∃ (h : pos ≠ s.startPos), (pos.prev h).get (by simp) = c := by
  simp [revMatchesAt_iff_exists_isLongestRevMatchAt, isLongestRevMatchAt_iff, exists_comm]

theorem matchesAt_iff_splits {c : Char} {s : Slice} {pos : s.Pos} :
    MatchesAt c pos ↔ ∃ t₁ t₂, pos.Splits t₁ (singleton c ++ t₂) := by
  rw [matchesAt_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨h, rfl⟩
    exact ⟨_, _, pos.splits_next_right h⟩
  · rintro ⟨t₁, t₂, hs⟩
    have hne := hs.ne_endPos_of_singleton
    exact ⟨hne, (singleton_append_inj.mp (hs.eq_right (pos.splits_next_right hne))).1.symm⟩

theorem revMatchesAt_iff_splits {c : Char} {s : Slice} {pos : s.Pos} :
    RevMatchesAt c pos ↔ ∃ t₁ t₂, pos.Splits (t₁ ++ singleton c) t₂ := by
  rw [revMatchesAt_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨h, rfl⟩
    exact ⟨_, _, pos.splits_prev_right h⟩
  · rintro ⟨t₁, t₂, hs⟩
    have hne := hs.ne_startPos_of_singleton
    refine ⟨hne, ?_⟩
    have := hs.eq_left (pos.splits_prev_right hne)
    simp only [append_singleton, push_inj] at this
    exact this.2.symm

theorem not_matchesAt_of_get_ne {c : Char} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : pos.get h ≠ c) : ¬ MatchesAt c pos := by
  simp [matchesAt_iff, hc]

theorem not_revMatchesAt_of_get_ne {c : Char} {s : Slice} {pos : s.Pos} {h : pos ≠ s.startPos}
    (hc : (pos.prev h).get (by simp) ≠ c) : ¬ RevMatchesAt c pos := by
  simp [revMatchesAt_iff, hc]

theorem matchAt?_eq {s : Slice} {pos : s.Pos} {c : Char} :
    matchAt? c pos =
      if h₀ : ∃ (h : pos ≠ s.endPos), pos.get h = c then some (pos.next h₀.1) else none := by
  split <;> simp_all [isLongestMatchAt_iff, matchesAt_iff]

theorem revMatchAt?_eq {s : Slice} {pos : s.Pos} {c : Char} :
    revMatchAt? c pos =
      if h₀ : ∃ (h : pos ≠ s.startPos), (pos.prev h).get (by simp) = c then some (pos.prev h₀.1) else none := by
  split <;> simp_all [isLongestRevMatchAt_iff, revMatchesAt_iff]

theorem isMatch_iff_isMatch_beq {c : Char} {s : Slice} {pos : s.Pos} :
    IsMatch c pos ↔ IsMatch (· == c) pos := by
  simp [isMatch_iff, CharPred.isMatch_iff, beq_iff_eq]

theorem isRevMatch_iff_isRevMatch_beq {c : Char} {s : Slice} {pos : s.Pos} :
    IsRevMatch c pos ↔ IsRevMatch (· == c) pos := by
  simp [isRevMatch_iff, CharPred.isRevMatch_iff, beq_iff_eq]

theorem isLongestMatch_iff_isLongestMatch_beq {c : Char} {s : Slice} {pos : s.Pos} :
    IsLongestMatch c pos ↔ IsLongestMatch (· == c) pos := by
  simp [isLongestMatch_iff_isMatch, isMatch_iff_isMatch_beq]

theorem isLongestRevMatch_iff_isLongestRevMatch_beq {c : Char} {s : Slice} {pos : s.Pos} :
    IsLongestRevMatch c pos ↔ IsLongestRevMatch (· == c) pos := by
  simp [isLongestRevMatch_iff_isRevMatch, isRevMatch_iff_isRevMatch_beq]

theorem isLongestMatchAt_iff_isLongestMatchAt_beq {c : Char} {s : Slice}
    {pos pos' : s.Pos} :
    IsLongestMatchAt c pos pos' ↔ IsLongestMatchAt (· == c) pos pos' := by
  simp [Model.isLongestMatchAt_iff, isLongestMatch_iff_isLongestMatch_beq]

theorem isLongestMatchAtChain_iff_isLongestMatchAtChain_beq {c : Char} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAtChain c pos pos' ↔ IsLongestMatchAtChain (· == c) pos pos' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | nil => simp
    | cons p₁ p₂ p₃ h₁ h₂ ih => exact .cons _ _ _ (isLongestMatchAt_iff_isLongestMatchAt_beq.1 h₁) ih
  · induction h with
    | nil => simp
    | cons p₁ p₂ p₃ h₁ h₂ ih => exact .cons _ _ _ (isLongestMatchAt_iff_isLongestMatchAt_beq.2 h₁) ih

theorem isLongestMatchAtChain_iff {c : Char} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAtChain c pos pos' ↔ pos ≤ pos' ∧ ∀ pos'', pos ≤ pos'' → (h : pos'' < pos') → pos''.get (Pos.ne_endPos_of_lt h) = c := by
  simp [isLongestMatchAtChain_iff_isLongestMatchAtChain_beq, CharPred.isLongestMatchAtChain_iff]

theorem isLongestMatchAtChain_iff_toList {c : Char} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAtChain c pos pos' ↔
      ∃ (h : pos ≤ pos'), (s.slice pos pos' h).copy.toList = List.replicate (s.slice pos pos' h).copy.length c := by
  simp [isLongestMatchAtChain_iff_isLongestMatchAtChain_beq, CharPred.isLongestMatchAtChain_iff_toList,
    List.eq_replicate_iff]

theorem isLongestMatchAtChain_startPos_endPos_iff_toList {c : Char} {s : Slice} :
    IsLongestMatchAtChain c s.startPos s.endPos ↔ s.copy.toList = List.replicate s.copy.length c := by
  simp [isLongestMatchAtChain_iff_isLongestMatchAtChain_beq,
    CharPred.isLongestMatchAtChain_startPos_endPos_iff_toList, List.eq_replicate_iff]

theorem isLongestRevMatchAt_iff_isLongestRevMatchAt_beq {c : Char} {s : Slice}
    {pos pos' : s.Pos} :
    IsLongestRevMatchAt c pos pos' ↔ IsLongestRevMatchAt (· == c) pos pos' := by
  simp [Model.isLongestRevMatchAt_iff, isLongestRevMatch_iff_isLongestRevMatch_beq]

theorem isLongestRevMatchAtChain_iff_isLongestRevMatchAtChain_beq {c : Char} {s : Slice} {pos pos' : s.Pos} :
    IsLongestRevMatchAtChain c pos pos' ↔ IsLongestRevMatchAtChain (· == c) pos pos' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | nil => simp
    | cons p₂ p₃ _ hmatch ih => exact .cons _ _ _ ih (isLongestRevMatchAt_iff_isLongestRevMatchAt_beq.1 hmatch)
  · induction h with
    | nil => simp
    | cons p₂ p₃ _ hmatch ih => exact .cons _ _ _ ih (isLongestRevMatchAt_iff_isLongestRevMatchAt_beq.2 hmatch)

theorem isLongestRevMatchAtChain_iff {c : Char} {s : Slice} {pos pos' : s.Pos} :
    IsLongestRevMatchAtChain c pos pos' ↔ pos ≤ pos' ∧ ∀ pos'', pos ≤ pos'' → (h : pos'' < pos') → pos''.get (Pos.ne_endPos_of_lt h) = c := by
  simp [isLongestRevMatchAtChain_iff_isLongestRevMatchAtChain_beq, CharPred.isLongestRevMatchAtChain_iff]

theorem isLongestRevMatchAtChain_iff_toList {c : Char} {s : Slice} {pos pos' : s.Pos} :
    IsLongestRevMatchAtChain c pos pos' ↔
      ∃ (h : pos ≤ pos'), (s.slice pos pos' h).copy.toList = List.replicate (s.slice pos pos' h).copy.length c := by
  simp [isLongestRevMatchAtChain_iff_isLongestRevMatchAtChain_beq, CharPred.isLongestRevMatchAtChain_iff_toList,
    List.eq_replicate_iff]

theorem isLongestRevMatchAtChain_startPos_endPos_iff_toList {c : Char} {s : Slice} :
    IsLongestRevMatchAtChain c s.startPos s.endPos ↔ s.copy.toList = List.replicate s.copy.length c := by
  simp [isLongestRevMatchAtChain_iff_isLongestRevMatchAtChain_beq,
    CharPred.isLongestRevMatchAtChain_startPos_endPos_iff_toList, List.eq_replicate_iff]

theorem matchesAt_iff_matchesAt_beq {c : Char} {s : Slice} {pos : s.Pos} :
    MatchesAt c pos ↔ MatchesAt (· == c) pos := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_isLongestMatchAt_beq]

theorem revMatchesAt_iff_revMatchesAt_beq {c : Char} {s : Slice} {pos : s.Pos} :
    RevMatchesAt c pos ↔ RevMatchesAt (· == c) pos := by
  simp [revMatchesAt_iff_exists_isLongestRevMatchAt, isLongestRevMatchAt_iff_isLongestRevMatchAt_beq]

theorem matchAt?_eq_matchAt?_beq {c : Char} {s : Slice} {pos : s.Pos} :
    matchAt? c pos = matchAt? (· == c) pos := by
  refine Option.ext (fun pos' => ?_)
  simp [matchAt?_eq_some_iff, isLongestMatchAt_iff_isLongestMatchAt_beq]

theorem revMatchAt?_eq_revMatchAt?_beq {c : Char} {s : Slice} {pos : s.Pos} :
    revMatchAt? c pos = revMatchAt? (· == c) pos := by
  refine Option.ext (fun pos' => ?_)
  simp [revMatchAt?_eq_some_iff, isLongestRevMatchAt_iff_isLongestRevMatchAt_beq]

theorem isValidSearchFrom_iff_isValidSearchFrom_beq {c : Char} {s : Slice} {p : s.Pos}
    {l : List (SearchStep s)} : IsValidSearchFrom c p l ↔ IsValidSearchFrom (· == c) p l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | endPos => simpa using IsValidSearchFrom.endPos
    | matched => simp_all [IsValidSearchFrom.matched, isLongestMatchAt_iff_isLongestMatchAt_beq]
    | mismatched => simp_all [IsValidSearchFrom.mismatched, matchesAt_iff_matchesAt_beq]
  · induction h with
    | endPos => simpa using IsValidSearchFrom.endPos
    | matched => simp_all [IsValidSearchFrom.matched, isLongestMatchAt_iff_isLongestMatchAt_beq]
    | mismatched => simp_all [IsValidSearchFrom.mismatched, matchesAt_iff_matchesAt_beq]

theorem isValidRevSearchFrom_iff_isValidRevSearchFrom_beq {c : Char} {s : Slice} {p : s.Pos}
    {l : List (SearchStep s)} : IsValidRevSearchFrom c p l ↔ IsValidRevSearchFrom (· == c) p l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · induction h with
    | startPos => simpa using IsValidRevSearchFrom.startPos
    | matched => simp_all [IsValidRevSearchFrom.matched, isLongestRevMatchAt_iff_isLongestRevMatchAt_beq]
    | mismatched => simp_all [IsValidRevSearchFrom.mismatched, revMatchesAt_iff_revMatchesAt_beq]
  · induction h with
    | startPos => simpa using IsValidRevSearchFrom.startPos
    | matched => simp_all [IsValidRevSearchFrom.matched, isLongestRevMatchAt_iff_isLongestRevMatchAt_beq]
    | mismatched => simp_all [IsValidRevSearchFrom.mismatched, revMatchesAt_iff_revMatchesAt_beq]

instance {c : Char} : LawfulToForwardSearcherModel c where
  isValidSearchFrom_toList s := by
    simpa [toSearcher_eq, isValidSearchFrom_iff_isValidSearchFrom_beq] using
      LawfulToForwardSearcherModel.isValidSearchFrom_toList (pat := (· == c)) (s := s)

instance {c : Char} : LawfulToBackwardSearcherModel c where
  isValidRevSearchFrom_toList s := by
    simpa [toBackwardSearcher_eq, isValidRevSearchFrom_iff_isValidRevSearchFrom_beq] using
      LawfulToBackwardSearcherModel.isValidRevSearchFrom_toList (pat := (· == c)) (s := s)

end Pattern.Model.Char

theorem startsWith_char_eq_startsWith_beq {c : Char} {s : Slice} :
    s.startsWith c = s.startsWith (· == c) := (rfl)

theorem dropPrefix?_char_eq_dropPrefix?_beq {c : Char} {s : Slice} :
    s.dropPrefix? c = s.dropPrefix? (· == c) := (rfl)

theorem dropPrefix_char_eq_dropPrefix_beq {c : Char} {s : Slice} :
    s.dropPrefix c = s.dropPrefix (· == c) := (rfl)

theorem skipPrefix?_char_eq_skipPrefix?_beq {c : Char} {s : Slice} :
    s.skipPrefix? c = s.skipPrefix? (· == c) := (rfl)

theorem Pattern.ForwardPattern.skipPrefix?_char_eq_skipPrefix?_beq {c : Char} {s : Slice} :
    skipPrefix? c s = skipPrefix? (· == c) s := (rfl)

theorem Pos.skip?_char_eq_skip?_beq {c : Char} {s : Slice} {pos : s.Pos} :
    pos.skip? c = pos.skip? (· == c) := (rfl)

theorem Pos.skipWhile_char_eq_skipWhile_beq {c : Char} {s : Slice} (curr : s.Pos) :
    Pos.skipWhile curr c = Pos.skipWhile curr (· == c) := by
  fun_induction Pos.skipWhile curr c with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pos.skip?_char_eq_skip?_beq, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pos.skip?_char_eq_skip?_beq, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.skipWhile]
    simp [← Pos.skip?_char_eq_skip?_beq, h]

theorem skipPrefixWhile_char_eq_skipPrefixWhile_beq {c : Char} {s : Slice} :
    s.skipPrefixWhile c = s.skipPrefixWhile (· == c) :=
  Pos.skipWhile_char_eq_skipWhile_beq s.startPos

theorem dropWhile_char_eq_dropWhile_beq {c : Char} {s : Slice} :
    s.dropWhile c = s.dropWhile (· == c) := by
  simp only [dropWhile]; exact congrArg _ skipPrefixWhile_char_eq_skipPrefixWhile_beq

theorem takeWhile_char_eq_takeWhile_beq {c : Char} {s : Slice} :
    s.takeWhile c = s.takeWhile (· == c) := by
  simp only [takeWhile]; exact congrArg _ skipPrefixWhile_char_eq_skipPrefixWhile_beq

theorem all_char_eq_all_beq {c : Char} {s : Slice} :
    s.all c = s.all (· == c) := by
  simp only [all, skipPrefixWhile_char_eq_skipPrefixWhile_beq]

theorem find?_char_eq_find?_beq {c : Char} {s : Slice} :
    s.find? c = s.find? (· == c) :=
  (rfl)

theorem Pos.find?_char_eq_find?_beq {c : Char} {s : Slice} {p : s.Pos} :
    p.find? c = p.find? (· == c) :=
  (rfl)

theorem contains_char_eq_contains_beq {c : Char} {s : Slice} :
    s.contains c = s.contains (· == c) :=
  (rfl)

theorem endsWith_char_eq_endsWith_beq {c : Char} {s : Slice} :
    s.endsWith c = s.endsWith (· == c) := (rfl)

theorem skipSuffix?_char_eq_skipSuffix?_beq {c : Char} {s : Slice} :
    s.skipSuffix? c = s.skipSuffix? (· == c) := (rfl)

theorem dropSuffix?_char_eq_dropSuffix?_beq {c : Char} {s : Slice} :
    s.dropSuffix? c = s.dropSuffix? (· == c) := (rfl)

theorem dropSuffix_char_eq_dropSuffix_beq {c : Char} {s : Slice} :
    s.dropSuffix c = s.dropSuffix (· == c) := (rfl)

theorem Pattern.BackwardPattern.skipSuffix?_char_eq_skipSuffix?_beq {c : Char} {s : Slice} :
    skipSuffix? c s = skipSuffix? (· == c) s := (rfl)

theorem Pos.revSkip?_char_eq_revSkip?_beq {c : Char} {s : Slice} {pos : s.Pos} :
    pos.revSkip? c = pos.revSkip? (· == c) := (rfl)

theorem Pos.revSkipWhile_char_eq_revSkipWhile_beq {c : Char} {s : Slice} (curr : s.Pos) :
    Pos.revSkipWhile curr c = Pos.revSkipWhile curr (· == c) := by
  fun_induction Pos.revSkipWhile curr c with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pos.revSkip?_char_eq_revSkip?_beq, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pos.revSkip?_char_eq_revSkip?_beq, h, ih]
  | case3 pos h =>
    conv => rhs; rw [Pos.revSkipWhile]
    simp [← Pos.revSkip?_char_eq_revSkip?_beq, h]

theorem skipSuffixWhile_char_eq_skipSuffixWhile_beq {c : Char} {s : Slice} :
    s.skipSuffixWhile c = s.skipSuffixWhile (· == c) :=
  Pos.revSkipWhile_char_eq_revSkipWhile_beq s.endPos

theorem dropEndWhile_char_eq_dropEndWhile_beq {c : Char} {s : Slice} :
    s.dropEndWhile c = s.dropEndWhile (· == c) := by
  simp only [dropEndWhile]; exact congrArg _ skipSuffixWhile_char_eq_skipSuffixWhile_beq

theorem takeEndWhile_char_eq_takeEndWhile_beq {c : Char} {s : Slice} :
    s.takeEndWhile c = s.takeEndWhile (· == c) := by
  simp only [takeEndWhile]; exact congrArg _ skipSuffixWhile_char_eq_skipSuffixWhile_beq

theorem revFind?_char_eq_revFind?_beq {c : Char} {s : Slice} :
    s.revFind? c = s.revFind? (· == c) :=
  (rfl)

theorem Pos.revFind?_char_eq_revFind?_beq {c : Char} {s : Slice} {p : s.Pos} :
    p.revFind? c = p.revFind? (· == c) :=
  (rfl)

theorem revAll_char_eq_revAll_beq {c : Char} {s : Slice} :
    s.revAll c = s.revAll (· == c) := by
  simp [revAll, skipSuffixWhile_char_eq_skipSuffixWhile_beq]

end String.Slice
