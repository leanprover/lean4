/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Slice
public import Init.Data.String.Search
public import Init.Data.String.Lemmas.Pattern.Basic
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Init.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.String.Lemmas.Order
import Init.Data.String.Lemmas.Basic
import Init.Data.String.OrderInstances
import Init.Grind

public section

open Std String.Slice Pattern Pattern.Model

namespace String.Slice

theorem Pattern.Model.find?_eq_some_iff {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat]
    {σ : Slice → Type} [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice} {pos : s.Pos} :
    s.find? pat = some pos ↔ MatchesAt pat pos ∧ (∀ pos', pos' < pos → ¬ MatchesAt pat pos') := by
  rw [find?, ← Iter.findSome?_toList]
  suffices ∀ (l : List (SearchStep s)) (pos : s.Pos) (hl : IsValidSearchFrom pat pos l) (pos' : s.Pos),
      l.findSome? (fun | .matched s _ => some s | .rejected .. => none) = some pos' ↔
        pos ≤ pos' ∧ MatchesAt pat pos' ∧ ∀ pos'', pos ≤ pos'' → pos'' < pos' → ¬ MatchesAt pat pos'' by
    simpa using this (ToForwardSearcher.toSearcher pat s).toList s.startPos
      (LawfulToForwardSearcherModel.isValidSearchFrom_toList s) pos
  intro l pos hl pos'
  induction hl with
  | endPos => simp +contextual
  | matched h₁ _ _ => have := h₁.matchesAt; grind
  | mismatched => grind

theorem Pattern.Model.find?_eq_none_iff {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat]
    {σ : Slice → Type} [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice} :
    s.find? pat = none ↔ ∀ (pos : s.Pos), ¬ MatchesAt pat pos := by
  simp only [Option.eq_none_iff_forall_ne_some, ne_eq, find?_eq_some_iff, not_and,
    Classical.not_forall, Classical.not_not]
  refine ⟨fun _ pos => ?_, by grind⟩
  induction pos using WellFounded.induction Pos.wellFounded_lt with grind

@[simp]
theorem isSome_find? {ρ : Type} (pat : ρ) {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] {s : Slice} : (s.find? pat).isSome = s.contains pat := by
  rw [find?, contains, ← Iter.findSome?_toList, ← Iter.any_toList]
  induction (ToForwardSearcher.toSearcher pat s).toList <;> grind

@[simp]
theorem find?_eq_none_iff {ρ : Type} (pat : ρ) {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] {s : Slice} : s.find? pat = none ↔ s.contains pat = false := by
  rw [← Option.isNone_iff_eq_none, ← Option.isSome_eq_false_iff, isSome_find?]

theorem Pattern.Model.contains_eq_false_iff {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat]
    {σ : Slice → Type} [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice} :
    s.contains pat = false ↔ ∀ (pos : s.Pos), ¬ MatchesAt pat pos := by
  rw [← find?_eq_none_iff, Slice.find?_eq_none_iff]

theorem Pattern.Model.contains_eq_true_iff {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat]
    {σ : Slice → Type} [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice} :
    s.contains pat ↔ ∃ (pos : s.Pos), MatchesAt pat pos := by
  simp [← Bool.not_eq_false, contains_eq_false_iff]

theorem Pos.find?_eq_find?_sliceFrom {ρ : Type} {pat : ρ} {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, IteratorLoop (σ s) Id Id] [ToForwardSearcher pat σ]
    {s : Slice} {p : s.Pos} :
    p.find? pat = ((s.sliceFrom p).find? pat).map Pos.ofSliceFrom :=
  (rfl)

theorem Pattern.Model.posFind?_eq_some_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice} {pos pos' : s.Pos} :
    pos.find? pat = some pos' ↔ pos ≤ pos' ∧ MatchesAt pat pos' ∧ (∀ pos'', pos ≤ pos'' → pos'' < pos' → ¬ MatchesAt pat pos'') := by
  simp only [Pos.find?_eq_find?_sliceFrom, Option.map_eq_some_iff, find?_eq_some_iff,
    matchesAt_iff_matchesAt_ofSliceFrom]
  refine ⟨?_, ?_⟩
  · rintro ⟨pos', ⟨h₁, h₂⟩, rfl⟩
    refine ⟨Pos.le_ofSliceFrom, h₁, fun p hp₁ hp₂ => ?_⟩
    simpa using h₂ (Pos.sliceFrom _ _ hp₁) (Pos.sliceFrom_lt_iff.2 hp₂)
  · rintro ⟨h₁, h₂, h₃⟩
    refine ⟨Pos.sliceFrom _ _ h₁, ⟨by simpa using h₂, fun p hp₁ hp₂ => ?_⟩, by simp⟩
    exact h₃ (Pos.ofSliceFrom p) Slice.Pos.le_ofSliceFrom (Pos.lt_sliceFrom_iff.1 hp₁) hp₂

theorem Pattern.Model.posFind?_eq_none_iff {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    {σ : Slice → Type} [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, Iterators.Finite (σ s) Id]
    [∀ s, IteratorLoop (σ s) Id Id] [∀ s, LawfulIteratorLoop (σ s) Id Id]
    [ToForwardSearcher pat σ] [LawfulToForwardSearcherModel pat] {s : Slice} {pos : s.Pos} :
    pos.find? pat = none ↔ ∀ pos', pos ≤ pos' → ¬ MatchesAt pat pos' := by
  rw [Pos.find?_eq_find?_sliceFrom, Option.map_eq_none_iff, Pattern.Model.find?_eq_none_iff]
  simpa only [matchesAt_iff_matchesAt_ofSliceFrom] using ⟨fun h p hp =>
    by simpa using h (Pos.sliceFrom _ _ hp), fun h p => by simpa using h _ Pos.le_ofSliceFrom⟩

end Slice

theorem Pos.find?_eq_find?_toSlice {ρ : Type} {pat : ρ} {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, IteratorLoop (σ s) Id Id] [ToForwardSearcher pat σ]
    {s : String} {p : s.Pos} : p.find? pat = (p.toSlice.find? pat).map Pos.ofToSlice :=
  (rfl)

theorem find?_eq_find?_toSlice {ρ : Type} {pat : ρ} {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, IteratorLoop (σ s) Id Id] [ToForwardSearcher pat σ]
    {s : String} : s.find? pat = (s.toSlice.find? pat).map Pos.ofToSlice :=
  (rfl)

theorem contains_eq_contains_toSlice {ρ : Type} {pat : ρ} {σ : Slice → Type}
    [∀ s, Iterator (σ s) Id (SearchStep s)] [∀ s, IteratorLoop (σ s) Id Id] [ToForwardSearcher pat σ]
    {s : String} : s.contains pat = s.toSlice.contains pat :=
  (rfl)

end String
