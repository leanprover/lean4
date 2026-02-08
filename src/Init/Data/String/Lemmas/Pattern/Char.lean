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

namespace String.Slice.Pattern.Char

instance {c : Char} : ForwardPatternModel c where
  Matches s := s = String.singleton c
  not_matches_empty := by simp

instance {c : Char} : NoPrefixForwardPatternModel c :=
  .of_length_eq (by simp +contextual [ForwardPatternModel.Matches])

theorem isMatch_iff {c : Char} {s : Slice} {pos : s.Pos} :
    IsMatch c pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ s.startPos.get h = c := by
  simp only [Pattern.isMatch_iff, ForwardPatternModel.Matches]
  rw [sliceTo_copy_eq_iff_exists_splits]
  refine ⟨?_, ?_⟩
  · simp only [splits_singleton_iff]
    exact fun ⟨t₂, h, h₁, h₂, h₃⟩ => ⟨h, h₁, h₂⟩
  · rintro ⟨h, rfl, rfl⟩
    exact ⟨_, Slice.splits_next_startPos⟩

theorem isLongestMatch_iff {c : Char} {s : Slice} {pos : s.Pos} :
    IsLongestMatch c pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ s.startPos.get h = c := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

instance {c : Char} : LawfulForwardPatternModel c where
  dropPrefix?_eq_some_iff {s} pos := by
    simp [isLongestMatch_iff, ForwardPattern.dropPrefix?]
    exact ⟨fun ⟨h, h₁, h₂⟩ => ⟨h, h₂.symm, h₁⟩, fun ⟨h, h₁, h₂⟩ => ⟨h, h₂, h₁.symm⟩⟩

instance {c : Char} : LawfulToForwardSearcherModel c :=
  .defaultImplementation

end String.Slice.Pattern.Char
