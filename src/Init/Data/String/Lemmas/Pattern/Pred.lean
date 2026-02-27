/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Pred
public import Init.Data.String.Lemmas.Pattern.Basic
import Init.Data.Option.Lemmas
import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Order
import Init.Data.Order.Lemmas
import Init.Data.String.OrderInstances
import Init.Omega

public section

namespace String.Slice.Pattern.Model.CharPred

instance {p : Char → Bool} : ForwardPatternModel p where
  Matches s := ∃ c, s = singleton c ∧ p c
  not_matches_empty := by
    simp

instance {p : Char → Bool} : NoPrefixForwardPatternModel p :=
  .of_length_eq (by simp +contextual [ForwardPatternModel.Matches])

theorem isMatch_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    IsMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  simp only [Model.isMatch_iff, ForwardPatternModel.Matches, sliceTo_copy_eq_iff_exists_splits]
  refine ⟨?_, ?_⟩
  · simp only [splits_singleton_iff]
    refine fun ⟨c, ⟨t₂, h, h₁, h₂, h₃⟩, hc⟩ => ⟨h, h₁, h₂ ▸ hc⟩
  · rintro ⟨h, rfl, h'⟩
    exact ⟨s.startPos.get h, ⟨_, Slice.splits_next_startPos⟩, h'⟩

theorem isLongestMatch_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    IsLongestMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestMatchAt_iff {p : Char → Bool} {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAt p pos pos' ↔ ∃ h, pos' = pos.next h ∧ p (pos.get h) := by
  simp +contextual [Model.isLongestMatchAt_iff, isLongestMatch_iff, ← Pos.ofSliceFrom_inj,
    Pos.get_eq_get_ofSliceFrom, Pos.ofSliceFrom_next]

theorem isLongestMatchAt_of_get {p : Char → Bool} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : p (pos.get h)) : IsLongestMatchAt p pos (pos.next h) :=
  isLongestMatchAt_iff.2 ⟨h, by simp [hc]⟩

instance {p : Char → Bool} : LawfulForwardPatternModel p where
  dropPrefix?_eq_some_iff {s} pos := by
    simp [isLongestMatch_iff, ForwardPattern.dropPrefix?, and_comm, eq_comm (b := pos)]

instance {p : Char → Bool} : LawfulToForwardSearcherModel p :=
  .defaultImplementation

theorem matchesAt_iff {p : Char → Bool} {s : Slice} {pos : s.Pos} :
    MatchesAt p pos ↔ ∃ (h : pos ≠ s.endPos), p (pos.get h) := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff, exists_comm]

theorem not_matchesAt_of_get {p : Char → Bool} {s : Slice} {pos : s.Pos} {h : pos ≠ s.endPos}
    (hc : p (pos.get h) = false) : ¬ MatchesAt p pos := by
  simp [matchesAt_iff, hc]

theorem matchAt?_eq {s : Slice} {pos : s.Pos} {p : Char → Bool} :
    matchAt? p pos =
      if h₀ : ∃ (h : pos ≠ s.endPos), p (pos.get h) then some (pos.next h₀.1) else none := by
  split <;> simp_all [isLongestMatchAt_iff, matchesAt_iff]

namespace Decidable

instance {p : Char → Prop} [DecidablePred p] : ForwardPatternModel p where
  Matches := ForwardPatternModel.Matches (decide <| p ·)
  not_matches_empty := ForwardPatternModel.not_matches_empty (pat := (decide <| p ·))

instance {p : Char → Prop} [DecidablePred p] : NoPrefixForwardPatternModel p where
  eq_empty := NoPrefixForwardPatternModel.eq_empty (pat := (decide <| p ·))

theorem isMatch_iff_isMatch_decide {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsMatch p pos ↔ IsMatch (decide <| p ·) pos :=
  ⟨fun ⟨h⟩ => ⟨h⟩, fun ⟨h⟩ => ⟨h⟩⟩

theorem isMatch_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  simp [isMatch_iff_isMatch_decide, CharPred.isMatch_iff]

theorem isLongestMatch_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    IsLongestMatch p pos ↔
      ∃ (h : s.startPos ≠ s.endPos), pos = s.startPos.next h ∧ p (s.startPos.get h) := by
  rw [isLongestMatch_iff_isMatch, isMatch_iff]

theorem isLongestMatch_iff_isLongestMatch_decide {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos : s.Pos} : IsLongestMatch p pos ↔ IsLongestMatch (decide <| p ·) pos := by
  simp [isLongestMatch_iff_isMatch, isMatch_iff_isMatch_decide]

theorem isLongestMatchAt_iff_isLongestMatchAt_decide {p : Char → Prop} [DecidablePred p]
    {s : Slice} {pos pos' : s.Pos} :
    IsLongestMatchAt p pos pos' ↔ IsLongestMatchAt (decide <| p ·) pos pos' := by
  simp [Model.isLongestMatchAt_iff, isLongestMatch_iff_isLongestMatch_decide]

theorem isLongestMatchAt_iff {p : Char → Prop} [DecidablePred p] {s : Slice}
    {pos pos' : s.Pos} :
    IsLongestMatchAt p pos pos' ↔ ∃ h, pos' = pos.next h ∧ p (pos.get h) := by
  simp [isLongestMatchAt_iff_isLongestMatchAt_decide, CharPred.isLongestMatchAt_iff]

theorem isLongestMatchAt_of_get {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos}
    {h : pos ≠ s.endPos} (hc : p (pos.get h)) : IsLongestMatchAt p pos (pos.next h) :=
  isLongestMatchAt_iff.2 ⟨h, by simp [hc]⟩

theorem dropPrefix?_eq_dropPrefix?_decide {p : Char → Prop} [DecidablePred p] :
    ForwardPattern.dropPrefix? p = ForwardPattern.dropPrefix? (decide <| p ·) := rfl

instance {p : Char → Prop} [DecidablePred p] : LawfulForwardPatternModel p where
  dropPrefix?_eq_some_iff {s} pos := by
    rw [dropPrefix?_eq_dropPrefix?_decide, isLongestMatch_iff_isLongestMatch_decide]
    exact LawfulForwardPatternModel.dropPrefix?_eq_some_iff ..

instance {p : Char → Prop} [DecidablePred p] : LawfulToForwardSearcherModel p :=
  .defaultImplementation

theorem matchesAt_iff {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos} :
    MatchesAt p pos ↔ ∃ (h : pos ≠ s.endPos), p (pos.get h) := by
  simp [matchesAt_iff_exists_isLongestMatchAt, isLongestMatchAt_iff, exists_comm]

theorem not_matchesAt_of_get {p : Char → Prop} [DecidablePred p] {s : Slice} {pos : s.Pos}
    {h : pos ≠ s.endPos} (hc : ¬ p (pos.get h)) : ¬ MatchesAt p pos := by
  simp [matchesAt_iff, hc]

theorem matchAt?_eq {s : Slice} {pos : s.Pos} {p : Char → Prop} [DecidablePred p] :
    matchAt? p pos =
      if h₀ : ∃ (h : pos ≠ s.endPos), p (pos.get h) then some (pos.next h₀.1) else none := by
  split <;> simp_all [isLongestMatchAt_iff, matchesAt_iff]

end Decidable

end String.Slice.Pattern.Model.CharPred
