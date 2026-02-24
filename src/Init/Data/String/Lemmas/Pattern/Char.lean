/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Char
public import Init.Data.String.Lemmas.Pattern.Basic
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

instance {c : Char} : LawfulForwardPatternModel c where
  dropPrefix?_eq_some_iff {s} pos := by
    simp [isLongestMatch_iff, ForwardPattern.dropPrefix?, and_comm, eq_comm (b := pos)]

instance {c : Char} : LawfulToForwardSearcherModel c :=
  .defaultImplementation

theorem matchesAt_iff {c : Char} {s : Slice} {pos : s.Pos} :
    MatchesAt c pos ↔ ∃ (h : pos ≠ s.endPos), pos.get h = c := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff, exists_comm]

theorem matchAt?_eq {s : Slice} {pos : s.Pos} {c : Char} :
    matchAt? c pos =
      if h₀ : ∃ (h : pos ≠ s.endPos), pos.get h = c then some (pos.next h₀.1) else none := by
  split <;> simp_all [isLongestMatchAt_iff, matchesAt_iff]

end String.Slice.Pattern.Model.Char
