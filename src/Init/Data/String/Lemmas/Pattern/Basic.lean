/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

prelude
public import Init.Data.String.Pattern.Basic
public import Init.Data.String.Lemmas.Splits
public import Init.Data.Iterators.Consumers.Collect
import all Init.Data.String.Pattern.Basic
import Init.Data.String.OrderInstances
import Init.Data.String.Lemmas.IsEmpty
public import Init.Data.String.Lemmas.Basic
import Init.Data.String.Lemmas.Order
import Init.Data.String.Termination
import Init.Data.Order.Lemmas
import Init.ByCases
import Init.Data.Option.Lemmas
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.String.Lemmas.FindPos

set_option doc.verso true

public section

namespace String.Slice.Pattern.Model

/-!
This file develops basic theory around searching in strings.

We provide a typeclass for providing semantics to a pattern and then define the relevant notions
of matching a pattern that let us state compatibility typeclasses for {name}`ForwardPattern` and
{name}`ToForwardSearcher` as well as their backwards variants. These typeclasses can then be
required by correctness results for string functions which are implemented using the pattern
framework.
-/

/--
This data-carrying typeclass is used to give semantics to a pattern type that implements
{name}`ForwardPattern` and/or {name}`ToForwardSearcher` by providing an abstract, not necessarily
decidable {name}`PatternModel.Matches` predicate that implementations of {name}`ForwardPattern`
and {name}`ToForwardSearcher` can be validated against.

Correctness results for generic functions relying on the pattern infrastructure, for example the
correctness result for {name (scope := "Init.Data.String.Slice")}`String.Slice.split`, are then
stated in terms of {name}`PatternModel.Matches`, and can be specialized to specific patterns
from there.

The corresponding compatibility typeclasses are
{name (scope := "Init.Data.String.Lemmas.Pattern.Basic")}`String.Slice.Pattern.Model.LawfulForwardPatternModel`
and
{name (scope := "Init.Data.String.Lemmas.Pattern.Basic")}`String.Slice.Pattern.Model.LawfulToForwardSearcherModel`.
-/
class PatternModel {ρ : Type} (pat : ρ) : Type where
  /-- The predicate that says which strings match the pattern. -/
  Matches : String → Prop

/--
Type class for the condition that the empty string is not a match. This is necessary for the theory to
work out as there is just no reasonable notion of searching that works for the empty string that is
still specific enough to yield reasonably strong correctness results for operations based on
searching.
-/
class StrictPatternModel {ρ : Type} (pat : ρ) [PatternModel pat] : Prop where
  not_matches_empty : ¬ PatternModel.Matches pat ""

theorem not_matches_empty {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] :
    ¬ PatternModel.Matches pat "" :=
  StrictPatternModel.not_matches_empty

/--
Predicate stating that the region between the start of the slice {name}`s` and the position
{name}`endPos` matches the pattern {name}`pat`. Note that there might be a longer match, see
{name (scope := "Init.Data.String.Lemmas.Pattern.Basic")}`String.Slice.Pattern.IsLongestMatch`.
-/
structure IsMatch (pat : ρ) [PatternModel pat] {s : Slice} (endPos : s.Pos) : Prop where
  matches_copy : PatternModel.Matches pat (s.sliceTo endPos).copy

theorem IsMatch.ne_startPos {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : IsMatch pat pos) : pos ≠ s.startPos := by
  intro hc
  apply not_matches_empty (pat := pat)
  simpa [hc] using h.matches_copy

theorem isMatch_iff {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} :
    IsMatch pat pos ↔ PatternModel.Matches pat (s.sliceTo pos).copy :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem isMatch_iff_exists_splits {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} :
    IsMatch pat pos ↔ ∃ t₁ t₂, pos.Splits t₁ t₂ ∧ PatternModel.Matches pat t₁ := by
  rw [isMatch_iff]
  refine ⟨fun h => ⟨_, _, pos.splits, h⟩, fun ⟨t₁, t₂, h₁, h₂⟩ => ?_⟩
  rwa [h₁.eq_left pos.splits] at h₂

@[simp]
theorem isMatch_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice} (h : s.copy = t.copy) {pos : s.Pos} :
    IsMatch pat (pos.cast h) ↔ IsMatch pat pos := by
  simp [isMatch_iff]

@[simp]
theorem isMatch_sliceTo_iff {pat : ρ} [PatternModel pat] {s : Slice} {pos p : s.Pos} {h} :
    IsMatch pat (Pos.sliceTo p pos h) ↔ IsMatch pat pos := by
  simp [isMatch_iff]

@[simp]
theorem isMatch_ofSliceTo_iff {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {pos : (s.sliceTo p).Pos} :
    IsMatch pat (Pos.ofSliceTo pos) ↔ IsMatch pat pos := by
  rw [← isMatch_sliceTo_iff (p := p) (h := Pos.ofSliceTo_le), Pos.sliceTo_ofSliceTo]

/--
Predicate stating that the region between the position {name}`startPos` and the end of the slice
{name}`s` matches the pattern {name}`pat`. Note that there might be a longer match.
-/
structure IsRevMatch (pat : ρ) [PatternModel pat] {s : Slice} (startPos : s.Pos) : Prop where
  matches_copy : PatternModel.Matches pat (s.sliceFrom startPos).copy

theorem IsRevMatch.ne_endPos {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : IsRevMatch pat pos) : pos ≠ s.endPos := by
  intro hc
  apply not_matches_empty (pat := pat)
  simpa [hc] using h.matches_copy

theorem isRevMatch_iff {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} :
    IsRevMatch pat pos ↔ PatternModel.Matches pat (s.sliceFrom pos).copy :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem isRevMatch_iff_exists_splits {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} :
    IsRevMatch pat pos ↔ ∃ t₁ t₂, pos.Splits t₁ t₂ ∧ PatternModel.Matches pat t₂ := by
  rw [isRevMatch_iff]
  refine ⟨fun h => ⟨_, _, pos.splits, h⟩, fun ⟨t₁, t₂, h₁, h₂⟩ => ?_⟩
  rwa [h₁.eq_right pos.splits] at h₂

@[simp]
theorem isRevMatch_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice} (h : s.copy = t.copy) {pos : s.Pos} :
    IsRevMatch pat (pos.cast h) ↔ IsRevMatch pat pos := by
  simp [isRevMatch_iff]

@[simp]
theorem isRevMatch_sliceFrom_iff {pat : ρ} [PatternModel pat] {s : Slice} {pos p : s.Pos} {h} :
    IsRevMatch pat (Pos.sliceFrom p pos h) ↔ IsRevMatch pat pos := by
  simp [isRevMatch_iff]

@[simp]
theorem isRevMatch_ofSliceFrom_iff {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {pos : (s.sliceFrom p).Pos} :
    IsRevMatch pat (Pos.ofSliceFrom pos) ↔ IsRevMatch pat pos := by
  rw [← isRevMatch_sliceFrom_iff (p := p) (h := Pos.le_ofSliceFrom), Pos.sliceFrom_ofSliceFrom]

/--
Predicate stating that the region between the start of the slice {name}`s` and the position
{name}`pos` matches the pattern {name}`pat`, and that there is no longer match starting at the
beginning of the slice. This is what a correct matcher should match.

In some cases, being a match and being a longest match will coincide, see
{name (scope := "Init.Data.String.Lemmas.Pattern.Basic")}`String.Slice.Pattern.Model.NoPrefixPatternModel`.
-/
structure IsLongestMatch (pat : ρ) [PatternModel pat] {s : Slice} (pos : s.Pos) where
  isMatch : IsMatch pat pos
  not_isMatch : ∀ pos', pos < pos' → ¬ IsMatch pat pos'

theorem isLongestMatch_iff {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} :
    IsLongestMatch pat pos ↔ IsMatch pat pos ∧ ∀ pos', pos < pos' → ¬ IsMatch pat pos' :=
  ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

theorem IsLongestMatch.ne_startPos {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : IsLongestMatch pat pos) : pos ≠ s.startPos :=
  h.isMatch.ne_startPos

@[simp]
theorem not_isLongestMatch_startPos {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} :
    ¬IsLongestMatch pat s.startPos :=
  fun h => h.ne_startPos rfl

theorem IsLongestMatch.eq {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos}
    (h : IsLongestMatch pat pos) (h' : IsLongestMatch pat pos') : pos = pos' := by
  apply Std.le_antisymm
  · exact Std.not_lt.1 (fun hlt => h'.not_isMatch _ hlt h.isMatch)
  · exact Std.not_lt.1 (fun hlt => h.not_isMatch _ hlt h'.isMatch)

open Classical in
theorem IsMatch.exists_isLongestMatch {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} :
    IsMatch pat pos → ∃ (pos' : s.Pos), IsLongestMatch pat pos' := by
  induction pos using WellFounded.induction Pos.wellFounded_gt with | h pos ih
  intro h₁
  by_cases h₂ : ∃ pos', pos < pos' ∧ IsMatch pat pos'
  · obtain ⟨pos', hp₁, hp₂⟩ := h₂
    exact ih _ hp₁ hp₂
  · exact ⟨pos, ⟨h₁, fun p' hp₁ hp₂ => h₂ ⟨_, hp₁, hp₂⟩⟩⟩

theorem IsLongestMatch.le_of_isMatch {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos}
    (h : IsLongestMatch pat pos) (h' : IsMatch pat pos') : pos' ≤ pos :=
  Std.not_lt.1 (fun hlt => h.not_isMatch _ hlt h')

@[simp]
theorem isLongestMatch_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice}
    (hst : s.copy = t.copy) {pos : s.Pos} :
    IsLongestMatch pat (pos.cast hst) ↔ IsLongestMatch pat pos := by
  simp only [isLongestMatch_iff, isMatch_cast_iff, and_congr_right_iff]
  refine fun _ => ⟨fun h p hp => ?_, fun h p hp => ?_⟩
  · rw [← isMatch_cast_iff hst]
    exact h _ (by simpa)
  · have : p = (p.cast hst.symm).cast hst := by simp
    rw [this, isMatch_cast_iff hst]
    exact h _ (by rwa [this, Pos.cast_lt_cast_iff] at hp)

theorem IsLongestMatch.of_eq {pat : ρ} [PatternModel pat] {s t : Slice} {pos : s.Pos} {pos' : t.Pos}
    (h : IsLongestMatch pat pos) (h₁ : s.copy = t.copy) (h₂ : pos.cast h₁ = pos') :
    IsLongestMatch pat pos' := by
  subst h₂; simpa

theorem IsLongestMatch.sliceTo {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos}
    (h : IsLongestMatch pat pos) (p : s.Pos) (hp : pos ≤ p) : IsLongestMatch pat (Pos.sliceTo p pos hp) := by
  simp [isLongestMatch_iff] at ⊢ h
  refine ⟨h.1, fun p hp => ?_⟩
  rw [← isMatch_ofSliceTo_iff]
  exact h.2 _ (by simpa [Pos.sliceTo_lt_iff] using hp)

theorem isLongestMatch_of_ofSliceTo {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {pos : (s.sliceTo p).Pos}
    (h : IsLongestMatch pat (Pos.ofSliceTo pos)) : IsLongestMatch pat pos := by
  simpa using h.sliceTo p

/--
Predicate stating that the region between the start of the slice {name}`s` and the position
{name}`pos` matches the pattern {name}`pat`, and that there is no longer match starting at the
beginning of the slice. This is what a correct matcher should match.

In some cases, being a match and being a longest match will coincide, see
{name (scope := "Init.Data.String.Lemmas.Pattern.Basic")}`String.Slice.Pattern.Model.NoPrefixPatternModel`.
-/
structure IsLongestRevMatch (pat : ρ) [PatternModel pat] {s : Slice} (pos : s.Pos) where
  isRevMatch : IsRevMatch pat pos
  not_isRevMatch : ∀ pos', pos' < pos → ¬ IsRevMatch pat pos'

theorem isLongestRevMatch_iff {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} :
    IsLongestRevMatch pat pos ↔ IsRevMatch pat pos ∧ ∀ pos', pos' < pos → ¬ IsRevMatch pat pos' :=
  ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

theorem IsLongestRevMatch.ne_endPos {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : IsLongestRevMatch pat pos) : pos ≠ s.endPos :=
  h.isRevMatch.ne_endPos

@[simp]
theorem not_isLongestRevMatch_endPos {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} :
    ¬IsLongestRevMatch pat s.endPos :=
  fun h => h.ne_endPos rfl

theorem IsLongestRevMatch.eq {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos}
    (h : IsLongestRevMatch pat pos) (h' : IsLongestRevMatch pat pos') : pos = pos' := by
  apply Std.le_antisymm
  · exact Std.not_lt.1 (fun hlt => h.not_isRevMatch _ hlt h'.isRevMatch)
  · exact Std.not_lt.1 (fun hlt => h'.not_isRevMatch _ hlt h.isRevMatch)

open Classical in
theorem IsRevMatch.exists_isLongestRevMatch {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos} :
    IsRevMatch pat pos → ∃ (pos' : s.Pos), IsLongestRevMatch pat pos' := by
  induction pos using WellFounded.induction Pos.wellFounded_lt with | h pos ih
  intro h₁
  by_cases h₂ : ∃ pos', pos' < pos ∧ IsRevMatch pat pos'
  · obtain ⟨pos', hp₁, hp₂⟩ := h₂
    exact ih _ hp₁ hp₂
  · exact ⟨pos, ⟨h₁, fun p' hp₁ hp₂ => h₂ ⟨_, hp₁, hp₂⟩⟩⟩

theorem IsLongestRevMatch.le_of_isRevMatch {pat : ρ} [PatternModel pat] {s : Slice} {pos pos' : s.Pos}
    (h : IsLongestRevMatch pat pos) (h' : IsRevMatch pat pos') : pos ≤ pos' :=
  Std.not_lt.1 (fun hlt => h.not_isRevMatch _ hlt h')

@[simp]
theorem isLongestRevMatch_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice}
    (hst : s.copy = t.copy) {pos : s.Pos} :
    IsLongestRevMatch pat (pos.cast hst) ↔ IsLongestRevMatch pat pos := by
  simp only [isLongestRevMatch_iff, isRevMatch_cast_iff, and_congr_right_iff]
  refine fun _ => ⟨fun h p hp => ?_, fun h p hp => ?_⟩
  · rw [← isRevMatch_cast_iff hst]
    exact h _ (by simpa)
  · have : p = (p.cast hst.symm).cast hst := by simp
    rw [this, isRevMatch_cast_iff hst]
    exact h _ (by rwa [this, Pos.cast_lt_cast_iff] at hp)

theorem IsLongestRevMatch.of_eq {pat : ρ} [PatternModel pat] {s t : Slice} {pos : s.Pos} {pos' : t.Pos}
    (h : IsLongestRevMatch pat pos) (h₁ : s.copy = t.copy) (h₂ : pos.cast h₁ = pos') :
    IsLongestRevMatch pat pos' := by
  subst h₂; simpa

theorem IsLongestRevMatch.sliceFrom {pat : ρ} [PatternModel pat] {s : Slice} {pos : s.Pos}
    (h : IsLongestRevMatch pat pos) (p : s.Pos) (hp : p ≤ pos) : IsLongestRevMatch pat (Pos.sliceFrom p pos hp) := by
  simp [isLongestRevMatch_iff] at ⊢ h
  refine ⟨h.1, fun p' hp' => ?_⟩
  rw [← isRevMatch_ofSliceFrom_iff]
  exact h.2 _ (by simpa [Pos.lt_sliceFrom_iff] using hp')

theorem isLongestRevMatch_of_ofSliceFrom {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {pos : (s.sliceFrom p).Pos}
    (h : IsLongestRevMatch pat (Pos.ofSliceFrom pos)) : IsLongestRevMatch pat pos := by
  simpa using h.sliceFrom p

/--
Predicate stating that a match for a given pattern is never a proper prefix of another match.

This implies that the notion of match and longest match coincide.
-/
class NoPrefixPatternModel {ρ : Type} (pat : ρ) [PatternModel pat] : Prop where
  eq_empty (s t) : PatternModel.Matches pat s → PatternModel.Matches pat (s ++ t) → t = ""

theorem NoPrefixPatternModel.of_length_eq {ρ : Type} {pat : ρ} [PatternModel pat]
    (h : ∀ s t, PatternModel.Matches pat s → PatternModel.Matches pat t → s.length = t.length) :
    NoPrefixPatternModel pat where
  eq_empty s t hs ht := by simpa using h s _ hs ht

theorem isLongestMatch_iff_isMatch {ρ : Type} (pat : ρ) [PatternModel pat] [NoPrefixPatternModel pat]
    {s : Slice} {pos : s.Pos} : IsLongestMatch pat pos ↔ IsMatch pat pos := by
  refine ⟨fun h => h.isMatch, fun h => ⟨h, fun pos' hpos' hm => ?_⟩⟩
  obtain ⟨t₁, t₂, ht₁, ht₂⟩ := isMatch_iff_exists_splits.1 h
  obtain ⟨t₁', t₂', ht₁', ht₂'⟩ := isMatch_iff_exists_splits.1 hm
  obtain ⟨t₅, ht₅, ht₅', ht₅''⟩ := (ht₁.lt_iff_exists_eq_append ht₁').1 hpos'
  exact ht₅ (NoPrefixPatternModel.eq_empty _ _ ht₂ (ht₅' ▸ ht₂'))

/--
Predicate stating that a match for a given pattern is never a proper suffix of another match.

This implies that the notion of reverse match and longest reverse match coincide.
-/
class NoSuffixPatternModel {ρ : Type} (pat : ρ) [PatternModel pat] : Prop where
  eq_empty (s t) : PatternModel.Matches pat t → PatternModel.Matches pat (s ++ t) → s = ""

theorem NoSuffixPatternModel.of_length_eq {ρ : Type} {pat : ρ} [PatternModel pat]
    (h : ∀ s t, PatternModel.Matches pat s → PatternModel.Matches pat t → s.length = t.length) :
    NoSuffixPatternModel pat where
  eq_empty s t hs ht := by simpa using h t _ hs ht

theorem isLongestRevMatch_iff_isRevMatch {ρ : Type} (pat : ρ) [PatternModel pat] [NoSuffixPatternModel pat]
    {s : Slice} {pos : s.Pos} : IsLongestRevMatch pat pos ↔ IsRevMatch pat pos := by
  refine ⟨fun h => h.isRevMatch, fun h => ⟨h, fun pos' hpos' hm => ?_⟩⟩
  obtain ⟨t₁, t₂, ht₁, ht₂⟩ := isRevMatch_iff_exists_splits.1 h
  obtain ⟨t₁', t₂', ht₁', ht₂'⟩ := isRevMatch_iff_exists_splits.1 hm
  obtain ⟨t₅, ht₅, ht₅', ht₅''⟩ := (ht₁'.lt_iff_exists_eq_append ht₁).1 hpos'
  exact ht₅ (NoSuffixPatternModel.eq_empty _ _ ht₂ (ht₅'' ▸ ht₂'))

/--
Predicate stating that the slice formed by {name}`startPos` and {name}`endPos` contains a match
of {name}`pat` in {name}`s` and it is longest among matches starting at {name}`startPos`.
-/
structure IsLongestMatchAt (pat : ρ) [PatternModel pat] {s : Slice} (startPos endPos : s.Pos) : Prop where
  le : startPos ≤ endPos
  isLongestMatch_sliceFrom : IsLongestMatch pat (Slice.Pos.sliceFrom _ _ le)

theorem isLongestMatchAt_iff {pat : ρ} [PatternModel pat] {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAt pat pos₁ pos₂ ↔
      ∃ (h : pos₁ ≤ pos₂), IsLongestMatch pat (Slice.Pos.sliceFrom _ _ h) :=
  ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

theorem IsLongestMatchAt.lt {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestMatchAt pat startPos endPos) : startPos < endPos := by
  have := h.isLongestMatch_sliceFrom.ne_startPos
  rw [← Pos.startPos_lt_iff, ← Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff] at this
  simpa

theorem IsLongestMatchAt.ne {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestMatchAt pat startPos endPos) : startPos ≠ endPos :=
  Std.ne_of_lt h.lt

@[simp]
theorem not_isLongestMatchAt_self {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {startPos : s.Pos} :
    ¬IsLongestMatchAt pat startPos startPos :=
  fun h => h.ne rfl

theorem IsLongestMatchAt.eq {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos endPos' : s.Pos}
    (h : IsLongestMatchAt pat startPos endPos) (h' : IsLongestMatchAt pat startPos endPos') :
    endPos = endPos' := by
  simpa using h.isLongestMatch_sliceFrom.eq h'.isLongestMatch_sliceFrom

private theorem isLongestMatch_of_eq {pat : ρ} [PatternModel pat] {s t : Slice}
    {pos : s.Pos} {pos' : t.Pos} (h_eq : s = t) (h_pos : pos.offset = pos'.offset)
    (hm : IsLongestMatch pat pos) : IsLongestMatch pat pos' := by
  subst h_eq; exact (Slice.Pos.ext h_pos) ▸ hm

theorem isLongestMatchAt_iff_isLongestMatchAt_ofSliceFrom {pat : ρ} [PatternModel pat]
    {s : Slice} {base : s.Pos} {startPos endPos : (s.sliceFrom base).Pos} :
    IsLongestMatchAt pat startPos endPos ↔ IsLongestMatchAt pat (Pos.ofSliceFrom startPos) (Pos.ofSliceFrom endPos) := by
  constructor
  · intro h
    refine ⟨Slice.Pos.ofSliceFrom_le_ofSliceFrom_iff.mpr h.le, ?_⟩
    exact isLongestMatch_of_eq Slice.sliceFrom_sliceFrom
      (by simp [Pos.Raw.ext_iff]; omega) h.isLongestMatch_sliceFrom
  · intro h
    refine ⟨Slice.Pos.ofSliceFrom_le_ofSliceFrom_iff.mp h.le, ?_⟩
    exact isLongestMatch_of_eq Slice.sliceFrom_sliceFrom.symm
      (by simp [Pos.Raw.ext_iff]; omega) h.isLongestMatch_sliceFrom

theorem IsLongestMatch.isLongestMatchAt_ofSliceFrom {pat : ρ} [PatternModel pat] {s : Slice}
    {p₀ : s.Pos} {pos : (s.sliceFrom p₀).Pos} (h : IsLongestMatch pat pos) :
    IsLongestMatchAt pat p₀ (Slice.Pos.ofSliceFrom pos) where
  le := Slice.Pos.le_ofSliceFrom
  isLongestMatch_sliceFrom := by simpa

@[simp]
theorem isLongestMatchAt_startPos_iff {pat : ρ} [PatternModel pat] {s : Slice} {endPos : s.Pos} :
    IsLongestMatchAt pat s.startPos endPos ↔ IsLongestMatch pat endPos := by
  simpa [isLongestMatchAt_iff] using
    ⟨fun h => isLongestMatch_of_eq (by simp) (by simp) h,
     fun h => isLongestMatch_of_eq (by simp) (by simp) h⟩

theorem isLongestMatch_iff_isLongestMatchAt_ofSliceFrom {pat : ρ} [PatternModel pat]
    {s : Slice} {base : s.Pos} (endPos : (s.sliceFrom base).Pos) :
    IsLongestMatch pat endPos ↔ IsLongestMatchAt pat base (Pos.ofSliceFrom endPos) := by
  simp [← isLongestMatchAt_startPos_iff, isLongestMatchAt_iff_isLongestMatchAt_ofSliceFrom]

theorem IsLongestMatchAt.matches_slice {pat : ρ} [PatternModel pat] {s : Slice}
    {startPos endPos : s.Pos} (h : IsLongestMatchAt pat startPos endPos) :
    PatternModel.Matches pat (s.slice startPos endPos h.le).copy := by
  simpa using h.isLongestMatch_sliceFrom.isMatch.matches_copy

@[simp]
theorem isLongestMatchAt_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice} (hst : s.copy = t.copy)
    {startPos endPos : s.Pos} :
    IsLongestMatchAt pat (startPos.cast hst) (endPos.cast hst) ↔ IsLongestMatchAt pat startPos endPos := by
  simp [isLongestMatchAt_iff, Pos.sliceFrom_cast]

theorem IsLongestMatchAt.of_eq {pat : ρ} [PatternModel pat] {s t : Slice} {s₁ e₁ : s.Pos} {s₂ e₂ : t.Pos}
    (h : IsLongestMatchAt pat s₁ e₁) (h₁ : s.copy = t.copy) (h₂ : s₁.cast h₁ = s₂) (h₃ : e₁.cast h₁ = e₂) :
    IsLongestMatchAt pat s₂ e₂ := by
  subst h₂ h₃; simpa

theorem IsLongestMatchAt.sliceTo {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestMatchAt pat startPos endPos) (p : s.Pos) (hp : endPos ≤ p) :
    IsLongestMatchAt pat (Pos.sliceTo p startPos (by exact Std.le_trans h.le hp)) (Pos.sliceTo p endPos hp) := by
  simp only [isLongestMatchAt_iff, Pos.sliceTo_le_sliceTo_iff] at ⊢ h
  obtain ⟨h, hp'⟩ := h
  exact ⟨h, (hp'.sliceTo (Pos.sliceFrom startPos p (Std.le_trans h hp)) (by simpa)).of_eq (by simp) (by ext; simp)⟩

theorem isLongestMatchAt_of_ofSliceTo {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {startPos endPos : (s.sliceTo p).Pos}
    (h : IsLongestMatchAt pat (Pos.ofSliceTo startPos) (Pos.ofSliceTo endPos)) :
    IsLongestMatchAt pat startPos endPos := by
  simpa using h.sliceTo p Pos.ofSliceTo_le

/--
Predicate stating that the range between two positions of {name}`s` can be covered by longest
matches of the pattern within {name}`s`.
-/
inductive IsLongestMatchAtChain (pat : ρ) [PatternModel pat] {s : Slice} : s.Pos → s.Pos → Prop where
  | nil (p : s.Pos) : IsLongestMatchAtChain pat p p
  | cons (startPos middlePos endPos : s.Pos) : IsLongestMatchAt pat startPos middlePos →
      IsLongestMatchAtChain pat middlePos endPos → IsLongestMatchAtChain pat startPos endPos

attribute [simp] IsLongestMatchAtChain.nil

theorem IsLongestMatchAtChain.eq_of_isLongestMatchAt_self {pat : ρ} [PatternModel pat] {s : Slice}
    {startPos endPos : s.Pos} (h : IsLongestMatchAtChain pat startPos endPos) (h' : IsLongestMatchAt pat startPos startPos) :
    startPos = endPos := by
  induction h with
  | nil => rfl
  | cons p₁ p₂ p₃ h₁ h₂ ih =>
    obtain rfl : p₁ = p₂ := h'.eq h₁
    exact ih h₁

theorem IsLongestMatchAtChain.le {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestMatchAtChain pat startPos endPos) : startPos ≤ endPos := by
  induction h with
  | nil => exact Std.le_refl _
  | cons p₁ p₂ p₃ h₁ h₂ ih => exact Std.le_trans h₁.le ih

theorem IsLongestMatchAtChain.sliceTo {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestMatchAtChain pat startPos endPos) (p : s.Pos) (hp : endPos ≤ p) :
    IsLongestMatchAtChain pat (Pos.sliceTo p startPos (by exact Std.le_trans h.le hp)) (Pos.sliceTo p endPos hp) := by
  induction h with
  | nil => simp
  | cons p₁ p₂ p₃ h₁ h₂ ih => exact .cons _ _ _ (h₁.sliceTo p (Std.le_trans h₂.le hp)) (ih hp)

theorem isLongestMatchAtChain_of_ofSliceTo {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos}
    {startPos endPos : (s.sliceTo p).Pos} (h : IsLongestMatchAtChain pat (Pos.ofSliceTo startPos) (Pos.ofSliceTo endPos)) :
    IsLongestMatchAtChain pat startPos endPos := by
  simpa using h.sliceTo p Pos.ofSliceTo_le

/--
Predicate stating that the slice formed by {name}`startPos` and {name}`endPos` contains is a match
of {name}`pat` in {name}`s` and it is longest among matches ending at {name}`endPos`.
-/
structure IsLongestRevMatchAt (pat : ρ) [PatternModel pat] {s : Slice} (startPos endPos : s.Pos) : Prop where
  le : startPos ≤ endPos
  isLongestRevMatch_sliceTo : IsLongestRevMatch pat (Slice.Pos.sliceTo _ _ le)

theorem isLongestRevMatchAt_iff {pat : ρ} [PatternModel pat] {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestRevMatchAt pat pos₁ pos₂ ↔
      ∃ (h : pos₁ ≤ pos₂), IsLongestRevMatch pat (Slice.Pos.sliceTo _ _ h) :=
  ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

theorem IsLongestRevMatchAt.lt {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestRevMatchAt pat startPos endPos) : startPos < endPos := by
  have := h.isLongestRevMatch_sliceTo.ne_endPos
  rw [← Pos.lt_endPos_iff, ← Slice.Pos.ofSliceTo_lt_ofSliceTo_iff] at this
  simpa

theorem IsLongestRevMatchAt.ne {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestRevMatchAt pat startPos endPos) : startPos ≠ endPos :=
  Std.ne_of_lt h.lt

@[simp]
theorem not_isLongestRevMatchAt_self {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} {endPos : s.Pos} :
    ¬IsLongestRevMatchAt pat endPos endPos :=
  fun h => h.ne rfl

theorem IsLongestRevMatchAt.eq {pat : ρ} [PatternModel pat] {s : Slice} {startPos startPos' endPos : s.Pos}
    (h : IsLongestRevMatchAt pat startPos endPos) (h' : IsLongestRevMatchAt pat startPos' endPos) :
    startPos = startPos' := by
  simpa using h.isLongestRevMatch_sliceTo.eq h'.isLongestRevMatch_sliceTo

private theorem isLongestRevMatch_of_eq {pat : ρ} [PatternModel pat] {s t : Slice}
    {pos : s.Pos} {pos' : t.Pos} (h_eq : s = t) (h_pos : pos.offset = pos'.offset)
    (hm : IsLongestRevMatch pat pos) : IsLongestRevMatch pat pos' := by
  subst h_eq; exact (Slice.Pos.ext h_pos) ▸ hm

theorem isLongestRevMatchAt_iff_isLongestRevMatchAt_ofSliceTo {pat : ρ} [PatternModel pat]
    {s : Slice} {base : s.Pos} {startPos endPos : (s.sliceTo base).Pos} :
    IsLongestRevMatchAt pat startPos endPos ↔ IsLongestRevMatchAt pat (Pos.ofSliceTo startPos) (Pos.ofSliceTo endPos) := by
  constructor
  · intro h
    refine ⟨Slice.Pos.ofSliceTo_le_ofSliceTo_iff.mpr h.le, ?_⟩
    exact isLongestRevMatch_of_eq Slice.sliceTo_sliceTo (by simp) h.isLongestRevMatch_sliceTo
  · intro h
    refine ⟨Slice.Pos.ofSliceTo_le_ofSliceTo_iff.mp h.le, ?_⟩
    exact isLongestRevMatch_of_eq Slice.sliceTo_sliceTo.symm (by simp) h.isLongestRevMatch_sliceTo

theorem IsLongestRevMatch.isLongestRevMatchAt_ofSliceTo {pat : ρ} [PatternModel pat] {s : Slice}
    {p₀ : s.Pos} {pos : (s.sliceTo p₀).Pos} (h : IsLongestRevMatch pat pos) :
    IsLongestRevMatchAt pat (Slice.Pos.ofSliceTo pos) p₀ where
  le := Slice.Pos.ofSliceTo_le
  isLongestRevMatch_sliceTo := by simpa

@[simp]
theorem isLongestRevMatchAt_endPos_iff {pat : ρ} [PatternModel pat] {s : Slice} {startPos : s.Pos} :
    IsLongestRevMatchAt pat startPos s.endPos ↔ IsLongestRevMatch pat startPos := by
  simpa [isLongestRevMatchAt_iff] using
    ⟨fun h => isLongestRevMatch_of_eq (by simp) (by simp) h,
     fun h => isLongestRevMatch_of_eq (by simp) (by simp) h⟩

theorem isLongestRevMatch_iff_isLongestRevMatchAt_ofSliceTo {pat : ρ} [PatternModel pat]
    {s : Slice} {base : s.Pos} (startPos : (s.sliceTo base).Pos) :
    IsLongestRevMatch pat startPos ↔ IsLongestRevMatchAt pat (Pos.ofSliceTo startPos) base := by
  simp [← isLongestRevMatchAt_endPos_iff, isLongestRevMatchAt_iff_isLongestRevMatchAt_ofSliceTo]

theorem IsLongestRevMatchAt.matches_slice {pat : ρ} [PatternModel pat] {s : Slice}
    {startPos endPos : s.Pos} (h : IsLongestRevMatchAt pat startPos endPos) :
    PatternModel.Matches pat (s.slice startPos endPos h.le).copy := by
  simpa using h.isLongestRevMatch_sliceTo.isRevMatch.matches_copy

@[simp]
theorem isLongestRevMatchAt_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice} (hst : s.copy = t.copy)
    {startPos endPos : s.Pos} :
    IsLongestRevMatchAt pat (startPos.cast hst) (endPos.cast hst) ↔ IsLongestRevMatchAt pat startPos endPos := by
  simp [isLongestRevMatchAt_iff, Pos.sliceTo_cast]

theorem IsLongestRevMatchAt.of_eq {pat : ρ} [PatternModel pat] {s t : Slice} {s₁ e₁ : s.Pos} {s₂ e₂ : t.Pos}
    (h : IsLongestRevMatchAt pat s₁ e₁) (h₁ : s.copy = t.copy) (h₂ : s₁.cast h₁ = s₂) (h₃ : e₁.cast h₁ = e₂) :
    IsLongestRevMatchAt pat s₂ e₂ := by
  subst h₂ h₃; simpa

theorem IsLongestRevMatchAt.sliceFrom {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestRevMatchAt pat startPos endPos) (p : s.Pos) (hp : p ≤ startPos) :
    IsLongestRevMatchAt pat (Pos.sliceFrom p startPos hp) (Pos.sliceFrom p endPos (by exact Std.le_trans hp h.le)) := by
  simp only [isLongestRevMatchAt_iff, Pos.sliceFrom_le_sliceFrom_iff] at ⊢ h
  obtain ⟨h, hp'⟩ := h
  exact ⟨h, (hp'.sliceFrom (Pos.sliceTo endPos p (Std.le_trans hp h)) (by simpa)).of_eq (by simp) (by ext; simp)⟩

theorem isLongestRevMatchAt_of_ofSliceFrom {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos} {startPos endPos : (s.sliceFrom p).Pos}
    (h : IsLongestRevMatchAt pat (Pos.ofSliceFrom startPos) (Pos.ofSliceFrom endPos)) :
    IsLongestRevMatchAt pat startPos endPos := by
  simpa using h.sliceFrom p Pos.le_ofSliceFrom

/--
Predicate stating that the range between two positions of {name}`s` can be covered by longest
reverse matches of the pattern within {name}`s`.
-/
inductive IsLongestRevMatchAtChain (pat : ρ) [PatternModel pat] {s : Slice} : s.Pos → s.Pos → Prop where
  | nil (p : s.Pos) : IsLongestRevMatchAtChain pat p p
  | cons (startPos middlePos endPos : s.Pos) : IsLongestRevMatchAtChain pat startPos middlePos →
      IsLongestRevMatchAt pat middlePos endPos → IsLongestRevMatchAtChain pat startPos endPos

attribute [simp] IsLongestRevMatchAtChain.nil

theorem IsLongestRevMatchAtChain.eq_of_isLongestRevMatchAt_self {pat : ρ} [PatternModel pat] {s : Slice}
    {startPos endPos : s.Pos} (h : IsLongestRevMatchAtChain pat startPos endPos) (h' : IsLongestRevMatchAt pat endPos endPos) :
    startPos = endPos := by
  induction h with
  | nil => rfl
  | cons mid endP hchain hmatch ih =>
    obtain rfl := hmatch.eq h'
    exact ih hmatch

theorem IsLongestRevMatchAtChain.le {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestRevMatchAtChain pat startPos endPos) : startPos ≤ endPos := by
  induction h with
  | nil => exact Std.le_refl _
  | cons mid endP hchain hmatch ih => exact Std.le_trans ih hmatch.le

theorem IsLongestRevMatchAtChain.sliceFrom {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestRevMatchAtChain pat startPos endPos) (p : s.Pos) (hp : p ≤ startPos) :
    IsLongestRevMatchAtChain pat (Pos.sliceFrom p startPos hp) (Pos.sliceFrom p endPos (by exact Std.le_trans hp h.le)) := by
  induction h with
  | nil => simp
  | cons mid endP hchain hmatch ih => exact .cons _ _ _ ih (hmatch.sliceFrom p (Std.le_trans hp hchain.le))

theorem isLongestRevMatchAtChain_of_ofSliceFrom {pat : ρ} [PatternModel pat] {s : Slice} {p : s.Pos}
    {startPos endPos : (s.sliceFrom p).Pos} (h : IsLongestRevMatchAtChain pat (Pos.ofSliceFrom startPos) (Pos.ofSliceFrom endPos)) :
    IsLongestRevMatchAtChain pat startPos endPos := by
  simpa using h.sliceFrom p Pos.le_ofSliceFrom

/--
Predicate stating that there is a (longest) match starting at the given position.
-/
structure MatchesAt (pat : ρ) [PatternModel pat] {s : Slice} (pos : s.Pos) : Prop where
  exists_isLongestMatchAt : ∃ endPos, IsLongestMatchAt pat pos endPos

theorem matchesAt_iff_exists_isLongestMatchAt {pat : ρ} [PatternModel pat] {s : Slice}
    {pos : s.Pos} : MatchesAt pat pos ↔ ∃ endPos, IsLongestMatchAt pat pos endPos :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem matchesAt_iff_exists_isLongestMatch {pat : ρ} [PatternModel pat] {s : Slice}
    {pos : s.Pos} :
    MatchesAt pat pos ↔ ∃ (endPos : s.Pos), ∃ h, IsLongestMatch pat (pos.sliceFrom endPos h) :=
  ⟨fun ⟨p, h⟩ => ⟨p, h.le, h.isLongestMatch_sliceFrom⟩, fun ⟨p, h₁, h₂⟩ => ⟨p, ⟨h₁, h₂⟩⟩⟩

theorem matchesAt_iff_exists_isMatch {pat : ρ} [PatternModel pat] {s : Slice}
    {pos : s.Pos} :
    MatchesAt pat pos ↔ ∃ (endPos : s.Pos), ∃ h, IsMatch pat (pos.sliceFrom endPos h) := by
  refine ⟨fun ⟨p, h⟩ => ⟨p, h.le, h.isLongestMatch_sliceFrom.isMatch⟩, fun ⟨p, h₁, h₂⟩ => ?_⟩
  obtain ⟨q, hq⟩ := h₂.exists_isLongestMatch
  exact ⟨Pos.ofSliceFrom q,
    ⟨Std.le_trans h₁ (by simpa [← Pos.ofSliceFrom_le_ofSliceFrom_iff] using hq.le_of_isMatch h₂),
     by simpa using hq⟩⟩

@[simp]
theorem not_matchesAt_endPos {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} :
    ¬ MatchesAt pat s.endPos := by
  simp only [matchesAt_iff_exists_isMatch, Pos.endPos_le, exists_prop_eq]
  intro h
  simpa [← Pos.ofSliceFrom_inj] using h.ne_startPos

theorem matchesAt_iff_matchesAt_ofSliceFrom {pat : ρ} [PatternModel pat] {s : Slice} {base : s.Pos}
    {pos : (s.sliceFrom base).Pos} : MatchesAt pat pos ↔ MatchesAt pat (Pos.ofSliceFrom pos) := by
  simp only [matchesAt_iff_exists_isLongestMatchAt]
  constructor
  · rintro ⟨endPos, h⟩
    exact ⟨Pos.ofSliceFrom endPos, isLongestMatchAt_iff_isLongestMatchAt_ofSliceFrom.mp h⟩
  · rintro ⟨endPos, h⟩
    exact ⟨base.sliceFrom endPos (Std.le_trans Slice.Pos.le_ofSliceFrom h.le),
           isLongestMatchAt_iff_isLongestMatchAt_ofSliceFrom.mpr (by simpa using h)⟩

theorem IsLongestMatchAt.matchesAt {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestMatchAt pat startPos endPos) : MatchesAt pat startPos where
  exists_isLongestMatchAt := ⟨_, h⟩

@[simp]
theorem matchesAt_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice} (hst : s.copy = t.copy)
    {pos : s.Pos} : MatchesAt pat (pos.cast hst) ↔ MatchesAt pat pos := by
  simp only [matchesAt_iff_exists_isLongestMatchAt]
  refine ⟨fun ⟨endPos, h⟩ => ?_, fun ⟨endPos, h⟩ => ?_⟩
  · exact ⟨endPos.cast hst.symm, by simpa [← isLongestMatchAt_cast_iff hst]⟩
  · exact ⟨endPos.cast hst, by simpa⟩

/--
Predicate stating that there is a (longest) match ending at the given position.
-/
structure RevMatchesAt (pat : ρ) [PatternModel pat] {s : Slice} (pos : s.Pos) : Prop where
  exists_isLongestRevMatchAt : ∃ startPos, IsLongestRevMatchAt pat startPos pos

theorem revMatchesAt_iff_exists_isLongestRevMatchAt {pat : ρ} [PatternModel pat] {s : Slice}
    {pos : s.Pos} : RevMatchesAt pat pos ↔ ∃ startPos, IsLongestRevMatchAt pat startPos pos :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem revMatchesAt_iff_exists_isLongestRevMatch {pat : ρ} [PatternModel pat] {s : Slice}
    {pos : s.Pos} :
    RevMatchesAt pat pos ↔ ∃ (startPos : s.Pos), ∃ h, IsLongestRevMatch pat (pos.sliceTo startPos h) :=
  ⟨fun ⟨p, h⟩ => ⟨p, h.le, h.isLongestRevMatch_sliceTo⟩, fun ⟨p, h₁, h₂⟩ => ⟨p, ⟨h₁, h₂⟩⟩⟩

theorem revMatchesAt_iff_exists_isRevMatch {pat : ρ} [PatternModel pat] {s : Slice}
    {pos : s.Pos} :
    RevMatchesAt pat pos ↔ ∃ (startPos : s.Pos), ∃ h, IsRevMatch pat (pos.sliceTo startPos h) := by
  refine ⟨fun ⟨p, h⟩ => ⟨p, h.le, h.isLongestRevMatch_sliceTo.isRevMatch⟩, fun ⟨p, h₁, h₂⟩ => ?_⟩
  obtain ⟨q, hq⟩ := h₂.exists_isLongestRevMatch
  exact ⟨Pos.ofSliceTo q,
    ⟨Std.le_trans (by simpa [← Pos.ofSliceTo_le_ofSliceTo_iff] using hq.le_of_isRevMatch h₂) h₁,
     by simpa using hq⟩⟩

@[simp]
theorem not_revMatchesAt_startPos {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice} :
    ¬ RevMatchesAt pat s.startPos := by
  simp only [revMatchesAt_iff_exists_isRevMatch, Pos.le_startPos, exists_prop_eq]
  intro h
  simpa [← Pos.ofSliceTo_inj] using h.ne_endPos

theorem revMatchesAt_iff_revMatchesAt_ofSliceTo {pat : ρ} [PatternModel pat] {s : Slice} {base : s.Pos}
    {pos : (s.sliceTo base).Pos} : RevMatchesAt pat pos ↔ RevMatchesAt pat (Pos.ofSliceTo pos) := by
  simp only [revMatchesAt_iff_exists_isLongestRevMatchAt]
  constructor
  · rintro ⟨startPos, h⟩
    exact ⟨Pos.ofSliceTo startPos, isLongestRevMatchAt_iff_isLongestRevMatchAt_ofSliceTo.mp h⟩
  · rintro ⟨startPos, h⟩
    exact ⟨base.sliceTo startPos (Std.le_trans h.le Slice.Pos.ofSliceTo_le),
           isLongestRevMatchAt_iff_isLongestRevMatchAt_ofSliceTo.mpr (by simpa using h)⟩

theorem IsLongestRevMatchAt.revMatchesAt {pat : ρ} [PatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestRevMatchAt pat startPos endPos) : RevMatchesAt pat endPos where
  exists_isLongestRevMatchAt := ⟨_, h⟩

@[simp]
theorem revMatchesAt_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice} (hst : s.copy = t.copy)
    {pos : s.Pos} : RevMatchesAt pat (pos.cast hst) ↔ RevMatchesAt pat pos := by
  simp only [revMatchesAt_iff_exists_isLongestRevMatchAt]
  refine ⟨fun ⟨endPos, h⟩ => ?_, fun ⟨endPos, h⟩ => ?_⟩
  · exact ⟨endPos.cast hst.symm, by simpa [← isLongestRevMatchAt_cast_iff hst]⟩
  · exact ⟨endPos.cast hst, by simpa⟩

open Classical in
/--
Noncomputable model function returning the end point of the longest match starting at the given
position, or {lean}`none` if there is no match.
-/
noncomputable def matchAt? {ρ : Type} (pat : ρ) [PatternModel pat]
    {s : Slice} (startPos : s.Pos) : Option s.Pos :=
  if h : ∃ endPos, IsLongestMatchAt pat startPos endPos then some h.choose else none

@[simp]
theorem matchAt?_eq_some_iff {ρ : Type} {pat : ρ} [PatternModel pat]
    {s : Slice} {startPos endPos : s.Pos} :
    matchAt? pat startPos = some endPos ↔ IsLongestMatchAt pat startPos endPos := by
  fun_cases matchAt? with
  | case1 h => simpa using ⟨by rintro rfl; exact h.choose_spec, fun h' => h.choose_spec.eq h'⟩
  | case2 => simp_all

@[simp]
theorem matchAt?_eq_none_iff {ρ : Type} {pat : ρ} [PatternModel pat]
    {s : Slice} {startPos : s.Pos} :
    matchAt? pat startPos = none ↔ ¬ MatchesAt pat startPos := by
  fun_cases matchAt? with
  | case1 h => simpa using ⟨h⟩
  | case2 h => simpa using fun ⟨h'⟩ => h h'

theorem lt_of_matchAt?_eq_some {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    {s : Slice} {startPos endPos : s.Pos} (h : matchAt? pat startPos = some endPos) :
    startPos < endPos :=
  (matchAt?_eq_some_iff.1 h).lt

@[simp]
theorem matchAt?_cast {ρ : Type} (pat : ρ) [PatternModel pat] {s t : Slice} (hst : s.copy = t.copy)
    {startPos : s.Pos} :
    matchAt? pat (startPos.cast hst) = (matchAt? pat startPos).map (Slice.Pos.cast · hst) := by
  refine Option.ext (fun endPos => ?_)
  have : endPos = (endPos.cast hst.symm).cast hst := by simp
  conv => lhs; rw [this, matchAt?_eq_some_iff, isLongestMatchAt_cast_iff]
  simp only [Option.map_eq_some_iff, matchAt?_eq_some_iff]
  exact ⟨fun h => ⟨_, ⟨h, by simp⟩⟩, by rintro ⟨pos, h, rfl⟩; simpa⟩

open Classical in
/--
Noncomputable model function returning the start point of the longest match ending at the given
position, or {lean}`none` if there is no match.
-/
noncomputable def revMatchAt? {ρ : Type} (pat : ρ) [PatternModel pat]
    {s : Slice} (endPos : s.Pos) : Option s.Pos :=
  if h : ∃ startPos, IsLongestRevMatchAt pat startPos endPos then some h.choose else none

@[simp]
theorem revMatchAt?_eq_some_iff {ρ : Type} {pat : ρ} [PatternModel pat]
    {s : Slice} {startPos endPos : s.Pos} :
    revMatchAt? pat endPos = some startPos ↔ IsLongestRevMatchAt pat startPos endPos := by
  fun_cases revMatchAt? with
  | case1 h => simpa using ⟨by rintro rfl; exact h.choose_spec, fun h' => h.choose_spec.eq h'⟩
  | case2 => simp_all

@[simp]
theorem revMatchAt?_eq_none_iff {ρ : Type} {pat : ρ} [PatternModel pat]
    {s : Slice} {endPos : s.Pos} :
    revMatchAt? pat endPos = none ↔ ¬ RevMatchesAt pat endPos := by
  fun_cases revMatchAt? with
  | case1 h => simpa using ⟨h⟩
  | case2 h => simpa using fun ⟨h'⟩ => h h'

theorem lt_of_revMatchAt?_eq_some {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    {s : Slice} {startPos endPos : s.Pos} (h : revMatchAt? pat endPos = some startPos) :
    startPos < endPos :=
  (revMatchAt?_eq_some_iff.1 h).lt

@[simp]
theorem revMatchAt?_cast {ρ : Type} (pat : ρ) [PatternModel pat] {s t : Slice} (hst : s.copy = t.copy)
    {startPos : s.Pos} :
    revMatchAt? pat (startPos.cast hst) = (revMatchAt? pat startPos).map (Slice.Pos.cast · hst) := by
  refine Option.ext (fun endPos => ?_)
  have : endPos = (endPos.cast hst.symm).cast hst := by simp
  conv => lhs; rw [this, revMatchAt?_eq_some_iff, isLongestRevMatchAt_cast_iff]
  simp only [Option.map_eq_some_iff, revMatchAt?_eq_some_iff]
  exact ⟨fun h => ⟨_, ⟨h, by simp⟩⟩, by rintro ⟨pos, h, rfl⟩; simpa⟩

/--
Predicate stating compatibility between {name}`PatternModel` and {name}`ForwardPattern`.

This extends {name}`LawfulForwardPattern`, but it is much stronger because it forces the
{name}`ForwardPattern` to match the longest prefix of the given slice that matches the property
supplied by the {name}`PatternModel` instance.
-/
class LawfulForwardPatternModel {ρ : Type} (pat : ρ) [ForwardPattern pat]
    [PatternModel pat] : Prop extends LawfulForwardPattern pat where
  skipPrefix?_eq_some_iff (pos) : ForwardPattern.skipPrefix? pat s = some pos ↔ IsLongestMatch pat pos

theorem LawfulForwardPatternModel.skipPrefix?_sliceFrom_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice} {p₀ : s.Pos} :
    ForwardPattern.skipPrefix? pat (s.sliceFrom p₀) = none ↔ ¬ MatchesAt pat p₀ := by
  classical
  rw [← Decidable.not_iff_not]
  simp [Option.ne_none_iff_exists', LawfulForwardPatternModel.skipPrefix?_eq_some_iff]
  refine ⟨fun ⟨p, hp⟩ => ?_, fun ⟨p, hp⟩ => ?_⟩
  · exact ⟨Slice.Pos.ofSliceFrom p, hp.isLongestMatchAt_ofSliceFrom⟩
  · exact ⟨p₀.sliceFrom p hp.le, hp.isLongestMatch_sliceFrom⟩

theorem LawfulForwardPatternModel.skipPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] [PatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice} :
    ForwardPattern.skipPrefix? pat s = none ↔ ¬ MatchesAt pat s.startPos := by
  conv => lhs; rw [← sliceFrom_startPos (s := s)]
  simp [skipPrefix?_sliceFrom_eq_none_iff]

/--
Predicate stating compatibility between {name}`PatternModel` and {name}`BackwardPattern`.

This extends {name}`LawfulBackwardPattern`, but it is much stronger because it forces the
{name}`BackwardPattern` to match the longest prefix of the given slice that matches the property
supplied by the {name}`PatternModel` instance.
-/
class LawfulBackwardPatternModel {ρ : Type} (pat : ρ) [BackwardPattern pat]
    [PatternModel pat] : Prop extends LawfulBackwardPattern pat where
  skipSuffix?_eq_some_iff (pos) : BackwardPattern.skipSuffix? pat s = some pos ↔ IsLongestRevMatch pat pos

theorem LawfulBackwardPatternModel.skipSuffix?_sliceTo_eq_none_iff {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat]
    [LawfulBackwardPatternModel pat] {s : Slice} {p₀ : s.Pos} :
    BackwardPattern.skipSuffix? pat (s.sliceTo p₀) = none ↔ ¬ RevMatchesAt pat p₀ := by
  classical
  rw [← Decidable.not_iff_not]
  simp [Option.ne_none_iff_exists', LawfulBackwardPatternModel.skipSuffix?_eq_some_iff]
  refine ⟨fun ⟨p, hp⟩ => ?_, fun ⟨p, hp⟩ => ?_⟩
  · exact ⟨Slice.Pos.ofSliceTo p, hp.isLongestRevMatchAt_ofSliceTo⟩
  · exact ⟨p₀.sliceTo p hp.le, hp.isLongestRevMatch_sliceTo⟩

theorem LawfulBackwardPatternModel.skipSuffix?_eq_none_iff {ρ : Type} {pat : ρ} [BackwardPattern pat] [PatternModel pat]
    [LawfulBackwardPatternModel pat] {s : Slice} :
    BackwardPattern.skipSuffix? pat s = none ↔ ¬ RevMatchesAt pat s.endPos := by
  conv => lhs; rw [← sliceTo_endPos (s := s)]
  simp [skipSuffix?_sliceTo_eq_none_iff]

/--
Inductive predicate stating that a list of search steps represents a valid search from a given
position in a slice.

"Searching" here means always taking the longest match at the first position where the pattern
matches.

Hence, this predicate determines the list of search steps up to grouping of rejections.
-/
inductive IsValidSearchFrom (pat : ρ) [PatternModel pat] {s : Slice} :
    s.Pos → List (SearchStep s) → Prop where
  | endPos : IsValidSearchFrom pat s.endPos []
  | matched {startPos endPos : s.Pos} :
      IsLongestMatchAt pat startPos endPos → IsValidSearchFrom pat endPos l →
      IsValidSearchFrom pat startPos (.matched startPos endPos :: l)
  | mismatched {startPos endPos : s.Pos} : startPos < endPos →
      (∀ pos, startPos ≤ pos → pos < endPos → ¬ MatchesAt pat pos) →
      IsValidSearchFrom pat endPos l → IsValidSearchFrom pat startPos (.rejected startPos endPos :: l)

theorem IsValidSearchFrom.matched_of_eq {pat : ρ} [PatternModel pat] {s : Slice}
    {startPos startPos' endPos : s.Pos} {l : List (SearchStep s)} (h₁ : IsValidSearchFrom pat endPos l)
    (h₂ : IsLongestMatchAt pat startPos' endPos)
    (h₃ : startPos = startPos') : IsValidSearchFrom pat startPos' (.matched startPos endPos :: l) := by
  cases h₃
  exact IsValidSearchFrom.matched h₂ h₁

theorem IsValidSearchFrom.mismatched_of_eq {pat : ρ} [PatternModel pat] {s : Slice}
    {startPos startPos' endPos : s.Pos} {l : List (SearchStep s)} (h₁ : IsValidSearchFrom pat endPos l)
      (h₀ : startPos' < endPos)
      (h₂ : ∀ pos, startPos' ≤ pos → pos < endPos → ¬ MatchesAt pat pos) (h₃ : startPos = startPos') :
      IsValidSearchFrom pat startPos' (.rejected startPos endPos :: l) := by
  cases h₃
  exact IsValidSearchFrom.mismatched h₀ h₂ h₁

theorem IsValidSearchFrom.endPos_of_eq {pat : ρ} [PatternModel pat] {s : Slice}
    {p : s.Pos} {l : List (SearchStep s)} (hp : p = s.endPos) (hl : l = []) :
    IsValidSearchFrom pat p l := by
  cases hp
  cases hl
  exact IsValidSearchFrom.endPos

theorem isValidSearchFrom_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice} (hst : s.copy = t.copy)
    {pos : s.Pos} {l : List (SearchStep t)} :
    IsValidSearchFrom pat (pos.cast hst) l ↔ IsValidSearchFrom pat pos (l.map (·.cast hst.symm)) := by
  suffices ∀ (s t : Slice) (hst : s.copy = t.copy) (pos : s.Pos) (l : List (SearchStep s)),
      IsValidSearchFrom pat pos l → IsValidSearchFrom pat (pos.cast hst) (l.map (·.cast hst)) from
    ⟨fun h => by simpa using this _ _ hst.symm _ _ h, fun h => by
      have hcomp : (SearchStep.cast hst) ∘ (SearchStep.cast hst.symm) = id := by ext; simp
      simpa [hcomp] using this _ _ hst _ _ h⟩
  intro s t hst pos l hl
  induction hl with
  | endPos => simpa using IsValidSearchFrom.endPos
  | matched h₁ h₂ ih =>
    simpa only [List.map_cons, SearchStep.cast_matched] using IsValidSearchFrom.matched (by simpa) ih
  | mismatched h₁ h₂ h₃ ih =>
    simp only [List.map_cons, SearchStep.cast_rejected]
    refine IsValidSearchFrom.mismatched (by simpa) (fun p hp₁ hp₂ hp₃ => ?_) ih
    exact h₂ (p.cast hst.symm) (by simpa [Pos.le_cast_iff]) (by simpa [Pos.cast_lt_iff]) (by simpa)

/--
Predicate stating compatibility between {name}`PatternModel` and {name}`ToForwardSearcher`.

We require the searcher to always match the longest match at the first position where the pattern
matches; see {name}`IsValidSearchFrom`.
-/
class LawfulToForwardSearcherModel {ρ : Type} (pat : ρ) [PatternModel pat] {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] : Prop where
  isValidSearchFrom_toList (s) : IsValidSearchFrom pat s.startPos (ToForwardSearcher.toSearcher pat s).toList

theorem LawfulToForwardSearcherModel.defaultImplementation {pat : ρ} [ForwardPattern pat] [StrictForwardPattern pat]
    [PatternModel pat] [LawfulForwardPatternModel pat] :
    letI : ToForwardSearcher pat (ToForwardSearcher.DefaultForwardSearcher pat) := .defaultImplementation
    LawfulToForwardSearcherModel pat := by
  let inst : ToForwardSearcher pat (ToForwardSearcher.DefaultForwardSearcher pat) := .defaultImplementation
  refine ⟨fun s => ?_⟩
  suffices ∀ (pos : s.Pos),
      IsValidSearchFrom pat pos (Std.Iter.mk (α := ToForwardSearcher.DefaultForwardSearcher pat s) ⟨pos⟩).toList from
    this s.startPos
  intro pos
  induction pos using WellFounded.induction Slice.Pos.wellFounded_gt with | h pos ih
  rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
  simp only [Std.Iter.toIterM, ne_eq]
  by_cases h : pos = s.endPos
  · simpa [h] using IsValidSearchFrom.endPos
  · simp only [h, ↓reduceDIte]
    split <;> rename_i heq
    · split at heq <;> rename_i pos' heq'
      · simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterStep.yield.injEq] at heq
        rw [← heq.1, ← heq.2]
        apply IsValidSearchFrom.matched
        · rw [LawfulForwardPattern.skipPrefixOfNonempty?_eq,
            LawfulForwardPatternModel.skipPrefix?_eq_some_iff] at heq'
          exact heq'.isLongestMatchAt_ofSliceFrom
        · simp only [Std.IterM.toIter]
          apply ih
          refine Std.lt_of_le_of_lt (Slice.Pos.le_ofSliceFrom (pos := Slice.startPos _))
            (Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff.2 ?_)
          simpa using StrictForwardPattern.ne_startPos _ _ heq'
      · simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterStep.yield.injEq] at heq
        rw [← heq.1, ← heq.2]
        apply IsValidSearchFrom.mismatched (by simp) _ (ih _ (by simp))
        intro p' hp' hp''
        obtain rfl : pos = p' := Std.le_antisymm hp' (by simpa using hp'')
        rwa [LawfulForwardPattern.skipPrefixOfNonempty?_eq,
          LawfulForwardPatternModel.skipPrefix?_sliceFrom_eq_none_iff] at heq'
    · split at heq <;> simp at heq
    · split at heq <;> simp at heq

/--
Inductive predicate stating that a list of search steps represents a valid backwards search from a
given position in a slice.

"Searching" here means always taking the longest match at the first position where the pattern
matches.

Hence, this predicate determines the list of search steps up to grouping of rejections.
-/
inductive IsValidRevSearchFrom (pat : ρ) [PatternModel pat] {s : Slice} :
    s.Pos → List (SearchStep s) → Prop where
  | startPos : IsValidRevSearchFrom pat s.startPos []
  | matched {startPos endPos : s.Pos} :
      IsLongestRevMatchAt pat startPos endPos → IsValidRevSearchFrom pat startPos l →
      IsValidRevSearchFrom pat endPos (.matched startPos endPos :: l)
  | mismatched {startPos endPos : s.Pos} : startPos < endPos →
      (∀ pos, startPos < pos → pos ≤ endPos → ¬ RevMatchesAt pat pos) →
      IsValidRevSearchFrom pat startPos l → IsValidRevSearchFrom pat endPos (.rejected startPos endPos :: l)

theorem IsValidRevSearchFrom.matched_of_eq {pat : ρ} [PatternModel pat] {s : Slice}
    {startPos endPos endPos' : s.Pos} {l : List (SearchStep s)} (h₁ : IsValidRevSearchFrom pat startPos l)
    (h₂ : IsLongestRevMatchAt pat startPos endPos')
    (h₃ : endPos = endPos') : IsValidRevSearchFrom pat endPos' (.matched startPos endPos :: l) := by
  cases h₃
  exact IsValidRevSearchFrom.matched h₂ h₁

theorem IsValidRevSearchFrom.mismatched_of_eq {pat : ρ} [PatternModel pat] {s : Slice}
    {startPos endPos endPos' : s.Pos} {l : List (SearchStep s)} (h₁ : IsValidRevSearchFrom pat startPos l)
      (h₀ : startPos < endPos')
      (h₂ : ∀ pos, startPos < pos → pos ≤ endPos' → ¬ RevMatchesAt pat pos) (h₃ : endPos = endPos') :
      IsValidRevSearchFrom pat endPos' (.rejected startPos endPos :: l) := by
  cases h₃
  exact IsValidRevSearchFrom.mismatched h₀ h₂ h₁

theorem IsValidRevSearchFrom.startPos_of_eq {pat : ρ} [PatternModel pat] {s : Slice}
    {p : s.Pos} {l : List (SearchStep s)} (hp : p = s.startPos) (hl : l = []) :
    IsValidRevSearchFrom pat p l := by
  cases hp
  cases hl
  exact IsValidRevSearchFrom.startPos

theorem isValidRevSearchFrom_cast_iff {pat : ρ} [PatternModel pat] {s t : Slice} (hst : s.copy = t.copy)
    {pos : s.Pos} {l : List (SearchStep t)} :
    IsValidRevSearchFrom pat (pos.cast hst) l ↔ IsValidRevSearchFrom pat pos (l.map (·.cast hst.symm)) := by
  suffices ∀ (s t : Slice) (hst : s.copy = t.copy) (pos : s.Pos) (l : List (SearchStep s)),
      IsValidRevSearchFrom pat pos l → IsValidRevSearchFrom pat (pos.cast hst) (l.map (·.cast hst)) from
    ⟨fun h => by simpa using this _ _ hst.symm _ _ h, fun h => by
      have hcomp : (SearchStep.cast hst) ∘ (SearchStep.cast hst.symm) = id := by ext; simp
      simpa [hcomp] using this _ _ hst _ _ h⟩
  intro s t hst pos l hl
  induction hl with
  | startPos => simpa using IsValidRevSearchFrom.startPos
  | matched h₁ h₂ ih =>
    simpa only [List.map_cons, SearchStep.cast_matched] using IsValidRevSearchFrom.matched (by simpa) ih
  | mismatched h₁ h₂ h₃ ih =>
    simp only [List.map_cons, SearchStep.cast_rejected]
    refine IsValidRevSearchFrom.mismatched (by simpa) (fun p hp₁ hp₂ hp₃ => ?_) ih
    exact h₂ (p.cast hst.symm) (by simpa [Pos.lt_cast_iff]) (by simpa [Pos.cast_le_iff]) (by simpa)

/--
Predicate stating compatibility between {name}`PatternModel` and {name}`ToBackwardSearcher`.

We require the searcher to always match the longest match at the first position where the pattern
matches; see {name}`IsValidRevSearchFrom`.
-/
class LawfulToBackwardSearcherModel {ρ : Type} (pat : ρ) [PatternModel pat] {σ : Slice → Type}
    [ToBackwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] : Prop where
  isValidRevSearchFrom_toList (s) : IsValidRevSearchFrom pat s.endPos (ToBackwardSearcher.toSearcher pat s).toList

theorem LawfulToBackwardSearcherModel.defaultImplementation {pat : ρ} [BackwardPattern pat] [StrictBackwardPattern pat]
    [PatternModel pat] [LawfulBackwardPatternModel pat] :
    letI : ToBackwardSearcher pat (ToBackwardSearcher.DefaultBackwardSearcher pat) := .defaultImplementation
    LawfulToBackwardSearcherModel pat := by
  let inst : ToBackwardSearcher pat (ToBackwardSearcher.DefaultBackwardSearcher pat) := .defaultImplementation
  refine ⟨fun s => ?_⟩
  suffices ∀ (pos : s.Pos),
      IsValidRevSearchFrom pat pos (Std.Iter.mk (α := ToBackwardSearcher.DefaultBackwardSearcher pat s) ⟨pos⟩).toList from
    this s.endPos
  intro pos
  induction pos using WellFounded.induction Slice.Pos.wellFounded_lt with | h pos ih
  rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
  simp only [Std.Iter.toIterM, ne_eq]
  by_cases h : pos = s.startPos
  · simpa [h] using IsValidRevSearchFrom.startPos
  · simp only [h, ↓reduceDIte]
    split <;> rename_i heq
    · split at heq <;> rename_i pos' heq'
      · simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterStep.yield.injEq] at heq
        rw [← heq.1, ← heq.2]
        apply IsValidRevSearchFrom.matched
        · rw [LawfulBackwardPattern.skipSuffixOfNonempty?_eq,
            LawfulBackwardPatternModel.skipSuffix?_eq_some_iff] at heq'
          exact heq'.isLongestRevMatchAt_ofSliceTo
        · simp only [Std.IterM.toIter]
          apply ih
          refine Std.lt_of_lt_of_le (Slice.Pos.ofSliceTo_lt_ofSliceTo_iff.2 ?_)
            (Slice.Pos.ofSliceTo_le (pos := Slice.endPos _))
          simpa using StrictBackwardPattern.ne_endPos _ _ heq'
      · simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
          Std.PlausibleIterStep.yield, Std.IterStep.yield.injEq] at heq
        rw [← heq.1, ← heq.2]
        apply IsValidRevSearchFrom.mismatched (by simp) _ (ih _ (by simp))
        intro p' hp' hp''
        obtain rfl : pos = p' := Std.le_antisymm (by simpa using hp') hp''
        rwa [LawfulBackwardPattern.skipSuffixOfNonempty?_eq,
          LawfulBackwardPatternModel.skipSuffix?_sliceTo_eq_none_iff] at heq'
    · split at heq <;> simp at heq
    · split at heq <;> simp at heq

end String.Slice.Pattern.Model
