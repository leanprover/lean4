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

public section

namespace String.Slice.Pattern.Model.Char

instance {c : Char} : ForwardPatternModel c where
  Matches s := s = String.singleton c
  not_matches_empty := by simp

instance {c : Char} : NoPrefixForwardPatternModel c :=
  .of_length_eq (by simp +contextual [ForwardPatternModel.Matches])

theorem isMatch_iff {c : Char} {s : Slice} {pos : s.Pos} :
    IsMatch c pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ s.startPos.get h = c := by
  simp only [Model.isMatch_iff, ForwardPatternModel.Matches, sliceTo_copy_eq_iff_exists_splits]
  refine ⟨?_, ?_⟩
  · simp only [splits_singleton_iff]
    exact fun ⟨t₂, h, h₁, h₂, h₃⟩ => ⟨h, h₁, h₂⟩
  · rintro ⟨h, rfl, rfl⟩
    exact ⟨_, Slice.splits_next_startPos⟩

theorem isLongestMatch_iff {c : Char} {s : Slice} {pos : s.Pos} :
    IsLongestMatch c pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ s.startPos.get h = c := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestMatchAt_iff {c : Char} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAt c pos pos' ↔ ∃ h, pos' = pos.next h ∧ pos.get h = c := by
  simp +contextual [Model.isLongestMatchAt_iff, isLongestMatch_iff, ← Pos.ofSliceFrom_inj,
    Pos.get_eq_get_ofSliceFrom, Pos.ofSliceFrom_next]

theorem isLongestMatchAt_of_get_eq {c : Char} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : pos.get h = c) : IsLongestMatchAt c pos (pos.next h) :=
  isLongestMatchAt_iff.2 ⟨h, by simp [hc]⟩

instance {c : Char} : LawfulForwardPatternModel c where
  dropPrefix?_eq_some_iff {s} pos := by
    simp [isLongestMatch_iff, ForwardPattern.dropPrefix?, and_comm, eq_comm (b := pos)]

theorem toSearcher_eq {c : Char} {s : Slice} :
  ToForwardSearcher.toSearcher c s = ToForwardSearcher.toSearcher (· == c) s := (rfl)

theorem matchesAt_iff {c : Char} {s : Slice} {pos : s.Pos} :
    MatchesAt c pos ↔ ∃ (h : pos ≠ s.endPos), pos.get h = c := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff, exists_comm]

theorem matchesAt_iff_splits {c : Char} {s : Slice} {pos : s.Pos} :
    MatchesAt c pos ↔ ∃ t₁ t₂, pos.Splits t₁ (singleton c ++ t₂) := by
  rw [matchesAt_iff]
  refine ⟨?_, ?_⟩
  · rintro ⟨h, rfl⟩
    exact ⟨_, _, pos.splits_next_right h⟩
  · rintro ⟨t₁, t₂, hs⟩
    have hne := hs.ne_endPos_of_singleton
    exact ⟨hne, (singleton_append_inj.mp (hs.eq_right (pos.splits_next_right hne))).1.symm⟩

theorem not_matchesAt_of_get_ne {c : Char} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : pos.get h ≠ c) : ¬ MatchesAt c pos := by
  simp [matchesAt_iff, hc]

theorem matchAt?_eq {s : Slice} {pos : s.Pos} {c : Char} :
    matchAt? c pos =
      if h₀ : ∃ (h : pos ≠ s.endPos), pos.get h = c then some (pos.next h₀.1) else none := by
  split <;> simp_all [isLongestMatchAt_iff, matchesAt_iff]

theorem isMatch_iff_isMatch_beq {c : Char} {s : Slice} {pos : s.Pos} :
    IsMatch c pos ↔ IsMatch (· == c) pos := by
  simp [isMatch_iff, CharPred.isMatch_iff, beq_iff_eq]

theorem isLongestMatch_iff_isLongestMatch_beq {c : Char} {s : Slice} {pos : s.Pos} :
    IsLongestMatch c pos ↔ IsLongestMatch (· == c) pos := by
  simp [isLongestMatch_iff_isMatch, isMatch_iff_isMatch_beq]

theorem isLongestMatchAt_iff_isLongestMatchAt_beq {c : Char} {s : Slice}
    {pos pos' : s.Pos} :
    IsLongestMatchAt c pos pos' ↔ IsLongestMatchAt (· == c) pos pos' := by
  simp [Model.isLongestMatchAt_iff, isLongestMatch_iff_isLongestMatch_beq]

theorem matchesAt_iff_matchesAt_beq {c : Char} {s : Slice} {pos : s.Pos} :
    MatchesAt c pos ↔ MatchesAt (· == c) pos := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff_isLongestMatchAt_beq]

theorem matchAt?_eq_matchAt?_beq {c : Char} {s : Slice} {pos : s.Pos} :
    matchAt? c pos = matchAt? (· == c) pos := by
  refine Option.ext (fun pos' => ?_)
  simp [matchAt?_eq_some_iff, isLongestMatchAt_iff_isLongestMatchAt_beq]

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

instance {c : Char} : LawfulToForwardSearcherModel c where
  isValidSearchFrom_toList s := by
    simpa [toSearcher_eq, isValidSearchFrom_iff_isValidSearchFrom_beq] using
      LawfulToForwardSearcherModel.isValidSearchFrom_toList (pat := (· == c)) (s := s)

end Pattern.Model.Char

theorem startsWith_char_eq_startsWith_beq {c : Char} {s : Slice} :
    s.startsWith c = s.startsWith (· == c) := (rfl)

theorem dropPrefix?_char_eq_dropPrefix?_beq {c : Char} {s : Slice} :
    s.dropPrefix? c = s.dropPrefix? (· == c) := (rfl)

theorem dropPrefix_char_eq_dropPrefix_beq {c : Char} {s : Slice} :
    s.dropPrefix c = s.dropPrefix (· == c) := (rfl)

theorem Pattern.ForwardPattern.dropPrefix?_char_eq_dropPrefix?_beq {c : Char} {s : Slice} :
    dropPrefix? c s = dropPrefix? (· == c) s := (rfl)

private theorem dropWhileGo_eq {c : Char} {s : Slice} (curr : s.Pos) :
    dropWhile.go s c curr = dropWhile.go s (· == c) curr := by
  fun_induction dropWhile.go s c curr with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [dropWhile.go]
    simp [← Pattern.ForwardPattern.dropPrefix?_char_eq_dropPrefix?_beq, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [dropWhile.go]
    simp [← Pattern.ForwardPattern.dropPrefix?_char_eq_dropPrefix?_beq, h, ih]
  | case3 pos h =>
    conv => rhs; rw [dropWhile.go]
    simp [← Pattern.ForwardPattern.dropPrefix?_char_eq_dropPrefix?_beq]

theorem dropWhile_char_eq_dropWhile_beq {c : Char} {s : Slice} :
    s.dropWhile c = s.dropWhile (· == c) := by
  simpa only [dropWhile] using dropWhileGo_eq s.startPos

private theorem takeWhileGo_eq {c : Char} {s : Slice} (curr : s.Pos) :
    takeWhile.go s c curr = takeWhile.go s (· == c) curr := by
  fun_induction takeWhile.go s c curr with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [takeWhile.go]
    simp [← Pattern.ForwardPattern.dropPrefix?_char_eq_dropPrefix?_beq, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [takeWhile.go]
    simp [← Pattern.ForwardPattern.dropPrefix?_char_eq_dropPrefix?_beq, h, ih]
  | case3 pos h =>
    conv => rhs; rw [takeWhile.go]
    simp [← Pattern.ForwardPattern.dropPrefix?_char_eq_dropPrefix?_beq]

theorem takeWhile_char_eq_takeWhile_beq {c : Char} {s : Slice} :
    s.takeWhile c = s.takeWhile (· == c) := by
  simp only [takeWhile]; exact takeWhileGo_eq s.startPos

theorem all_char_eq_all_beq {c : Char} {s : Slice} :
    s.all c = s.all (· == c) := by
  simp only [all, dropWhile_char_eq_dropWhile_beq]

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

theorem dropSuffix?_char_eq_dropSuffix?_beq {c : Char} {s : Slice} :
    s.dropSuffix? c = s.dropSuffix? (· == c) := (rfl)

theorem dropSuffix_char_eq_dropSuffix_beq {c : Char} {s : Slice} :
    s.dropSuffix c = s.dropSuffix (· == c) := (rfl)

theorem Pattern.BackwardPattern.dropSuffix?_char_eq_dropSuffix?_beq {c : Char} {s : Slice} :
    dropSuffix? c s = dropSuffix? (· == c) s := (rfl)

private theorem dropEndWhileGo_eq {c : Char} {s : Slice} (curr : s.Pos) :
    dropEndWhile.go s c curr = dropEndWhile.go s (· == c) curr := by
  fun_induction dropEndWhile.go s c curr with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [dropEndWhile.go]
    simp [← Pattern.BackwardPattern.dropSuffix?_char_eq_dropSuffix?_beq, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [dropEndWhile.go]
    simp [← Pattern.BackwardPattern.dropSuffix?_char_eq_dropSuffix?_beq, h, ih]
  | case3 pos h =>
    conv => rhs; rw [dropEndWhile.go]
    simp [← Pattern.BackwardPattern.dropSuffix?_char_eq_dropSuffix?_beq]

theorem dropEndWhile_char_eq_dropEndWhile_beq {c : Char} {s : Slice} :
    s.dropEndWhile c = s.dropEndWhile (· == c) := by
  simpa only [dropEndWhile] using dropEndWhileGo_eq s.endPos

private theorem takeEndWhileGo_eq {c : Char} {s : Slice} (curr : s.Pos) :
    takeEndWhile.go s c curr = takeEndWhile.go s (· == c) curr := by
  fun_induction takeEndWhile.go s c curr with
  | case1 pos nextCurr h₁ h₂ ih =>
    conv => rhs; rw [takeEndWhile.go]
    simp [← Pattern.BackwardPattern.dropSuffix?_char_eq_dropSuffix?_beq, h₁, h₂, ih]
  | case2 pos nextCurr h ih =>
    conv => rhs; rw [takeEndWhile.go]
    simp [← Pattern.BackwardPattern.dropSuffix?_char_eq_dropSuffix?_beq, h, ih]
  | case3 pos h =>
    conv => rhs; rw [takeEndWhile.go]
    simp [← Pattern.BackwardPattern.dropSuffix?_char_eq_dropSuffix?_beq]

theorem takeEndWhile_char_eq_takeEndWhile_beq {c : Char} {s : Slice} :
    s.takeEndWhile c = s.takeEndWhile (· == c) := by
  simpa only [takeEndWhile] using takeEndWhileGo_eq s.endPos

end String.Slice
