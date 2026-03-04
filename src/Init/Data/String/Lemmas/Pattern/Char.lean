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
import all Init.Data.String.Slice
public import Init.Data.String.Lemmas.Pattern.Pred
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

instance {c : Char} : LawfulToForwardSearcherModel c :=
  .defaultImplementation

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

end String.Slice.Pattern.Model.Char

end -- public section

/-! ### Slice-level operation bridges -/

namespace String.Slice

-- ForwardPattern bridges

theorem startsWith_eq_startsWith_beq {c : Char} {s : Slice} :
    s.startsWith c = s.startsWith (· == c) := rfl

theorem dropPrefix?_eq_dropPrefix?_beq {c : Char} {s : Slice} :
    s.dropPrefix? c = s.dropPrefix? (· == c) := rfl

theorem dropPrefix_eq_dropPrefix_beq {c : Char} {s : Slice} :
    s.dropPrefix c = s.dropPrefix (· == c) := rfl

private theorem dropWhile_go_beq_eq {c : Char} {s : Slice} (curr : s.Pos) :
    dropWhile.go s c curr = dropWhile.go s (· == c) curr := by
  unfold dropWhile.go
  simp only [show Pattern.ForwardPattern.dropPrefix? c (s.sliceFrom curr) =
    Pattern.ForwardPattern.dropPrefix? (· == c) (s.sliceFrom curr) from rfl]
  split
  · split
    · exact dropWhile_go_beq_eq ..
    · rfl
  · rfl
termination_by curr

theorem dropWhile_eq_dropWhile_beq {c : Char} {s : Slice} :
    s.dropWhile c = s.dropWhile (· == c) := by
  simp only [dropWhile]; exact dropWhile_go_beq_eq s.startPos

private theorem takeWhile_go_beq_eq {c : Char} {s : Slice} (curr : s.Pos) :
    takeWhile.go s c curr = takeWhile.go s (· == c) curr := by
  unfold takeWhile.go
  simp only [show Pattern.ForwardPattern.dropPrefix? c (s.sliceFrom curr) =
    Pattern.ForwardPattern.dropPrefix? (· == c) (s.sliceFrom curr) from rfl]
  split
  · split
    · exact takeWhile_go_beq_eq ..
    · rfl
  · rfl
termination_by curr

theorem takeWhile_eq_takeWhile_beq {c : Char} {s : Slice} :
    s.takeWhile c = s.takeWhile (· == c) := by
  simp only [takeWhile]; exact takeWhile_go_beq_eq s.startPos

theorem all_eq_all_beq {c : Char} {s : Slice} :
    s.all c = s.all (· == c) := by
  simp only [all, dropWhile_eq_dropWhile_beq]

-- BackwardPattern bridges

theorem endsWith_eq_endsWith_beq {c : Char} {s : Slice} :
    s.endsWith c = s.endsWith (· == c) := rfl

theorem dropSuffix?_eq_dropSuffix?_beq {c : Char} {s : Slice} :
    s.dropSuffix? c = s.dropSuffix? (· == c) := rfl

theorem dropSuffix_eq_dropSuffix_beq {c : Char} {s : Slice} :
    s.dropSuffix c = s.dropSuffix (· == c) := rfl

private theorem dropEndWhile_go_beq_eq {c : Char} {s : Slice} (curr : s.Pos) :
    dropEndWhile.go s c curr = dropEndWhile.go s (· == c) curr := by
  unfold dropEndWhile.go
  simp only [show Pattern.BackwardPattern.dropSuffix? c (s.sliceTo curr) =
    Pattern.BackwardPattern.dropSuffix? (· == c) (s.sliceTo curr) from rfl]
  split
  · split
    · exact dropEndWhile_go_beq_eq ..
    · rfl
  · rfl
termination_by curr.down

theorem dropEndWhile_eq_dropEndWhile_beq {c : Char} {s : Slice} :
    s.dropEndWhile c = s.dropEndWhile (· == c) := by
  simp only [dropEndWhile]; exact dropEndWhile_go_beq_eq s.endPos

private theorem takeEndWhile_go_beq_eq {c : Char} {s : Slice} (curr : s.Pos) :
    takeEndWhile.go s c curr = takeEndWhile.go s (· == c) curr := by
  unfold takeEndWhile.go
  simp only [show Pattern.BackwardPattern.dropSuffix? c (s.sliceTo curr) =
    Pattern.BackwardPattern.dropSuffix? (· == c) (s.sliceTo curr) from rfl]
  split
  · split
    · exact takeEndWhile_go_beq_eq ..
    · rfl
  · rfl
termination_by curr.down

theorem takeEndWhile_eq_takeEndWhile_beq {c : Char} {s : Slice} :
    s.takeEndWhile c = s.takeEndWhile (· == c) := by
  simp only [takeEndWhile]; exact takeEndWhile_go_beq_eq s.endPos

end String.Slice
