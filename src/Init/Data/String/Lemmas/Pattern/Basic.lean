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
import Init.Data.String.Lemmas.Order
import Init.Data.String.Termination
import Init.Data.Order.Lemmas
import Init.ByCases
import Init.Data.Option.Lemmas
import Init.Data.Iterators.Lemmas.Consumers.Collect

set_option doc.verso true

public section

namespace String.Slice.Pattern.Model

/-!
This file develops basic theory around searching in strings.

We provide a typeclass for providing semantics to a pattern and then define the relevant notions
of matching a pattern that let us state compatibility typeclasses for {name}`ForwardPattern` and
{name}`ToForwardSearcher`. These typeclasses can then be required by correctness results for
string functions which are implemented using the pattern framework.
-/

/--
This data-carrying typeclass is used to give semantics to a pattern type that implements
{name}`ForwardPattern` and/or {name}`ToForwardSearcher` by providing an abstract, not necessarily
decidable {name}`ForwardPatternModel.Matches` predicate that implementates of {name}`ForwardPattern`
and {name}`ToForwardSearcher` can be validated against.

Correctness results for generic functions relying on the pattern infrastructure, for example the
correctness result for {name (scope := "Init.Data.String.Slice")}`String.Slice.split`, are then
stated in terms of {name}`ForwardPatternModel.Matches`, and can be specialized to specific patterns
from there.

The corresponding compatibility typeclasses are
{name (scope := "Init.Data.String.Lemmas.Pattern.Basic")}`String.Slice.Pattern.Model.LawfulForwardPatternModel`
and
{name (scope := "Init.Data.String.Lemmas.Pattern.Basic")}`String.Slice.Pattern.Model.LawfulToForwardSearcherModel`.

We include the condition that the empty string is not a match. This is necessary for the theory to
work out as there is just no reasonable notion of searching that works for the empty string that is
still specific enough to yield reasonably strong correctness results for operations based on
searching.

This means that pattern types that allow searching for the empty string will have to special-case
the empty string in their correctness statements.
-/
class ForwardPatternModel {ρ : Type} (pat : ρ) : Type where
  /-- The predicate that says which strings match the pattern. -/
  Matches : String → Prop
  not_matches_empty : ¬ Matches ""

/--
Predicate stating that the region between the start of the slice {name}`s` and the position
{name}`endPos` matches the pattern {name}`pat`. Note that there might be a longer match, see
{name (scope := "Init.Data.String.Lemmas.Pattern.Basic")}`String.Slice.Pattern.IsLongestMatch`.
-/
structure IsMatch (pat : ρ) [ForwardPatternModel pat] {s : Slice} (endPos : s.Pos) : Prop where
  matches_copy : ForwardPatternModel.Matches pat (s.sliceTo endPos).copy

theorem IsMatch.ne_startPos {pat : ρ} [ForwardPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : IsMatch pat pos) : pos ≠ s.startPos := by
  intro hc
  apply ForwardPatternModel.not_matches_empty (pat := pat)
  simpa [hc] using h.matches_copy

theorem isMatch_iff {pat : ρ} [ForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    IsMatch pat pos ↔ ForwardPatternModel.Matches pat (s.sliceTo pos).copy :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem isMatch_iff_exists_splits {pat : ρ} [ForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    IsMatch pat pos ↔ ∃ t₁ t₂, pos.Splits t₁ t₂ ∧ ForwardPatternModel.Matches pat t₁ := by
  rw [isMatch_iff]
  refine ⟨fun h => ⟨_, _, pos.splits, h⟩, fun ⟨t₁, t₂, h₁, h₂⟩ => ?_⟩
  rwa [h₁.eq_left pos.splits] at h₂

/--
Predicate stating that the region between the start of the slice {name}`s` and the position
{name}`endPos` matches that pattern {name}`pat`, and that there is no longer match starting at the
beginning of the slice. This is what a correct matcher should match.

In some cases, being a match and being a longest match will coincide, see
{name (scope := "Init.Data.String.Lemmas.Pattern.Basic")}`String.Slice.Pattern.Model.NoPrefixForwardPatternModel`.
-/
structure IsLongestMatch (pat : ρ) [ForwardPatternModel pat] {s : Slice} (pos : s.Pos) where
  isMatch : IsMatch pat pos
  not_isMatch : ∀ pos', pos < pos' → ¬ IsMatch pat pos'

theorem IsLongestMatch.ne_startPos {pat : ρ} [ForwardPatternModel pat] {s : Slice} {pos : s.Pos}
    (h : IsLongestMatch pat pos) : pos ≠ s.startPos :=
  h.isMatch.ne_startPos

theorem IsLongestMatch.eq {pat : ρ} [ForwardPatternModel pat] {s : Slice} {pos pos' : s.Pos}
    (h : IsLongestMatch pat pos) (h' : IsLongestMatch pat pos') : pos = pos' := by
  apply Std.le_antisymm
  · exact Std.not_lt.1 (fun hlt => h'.not_isMatch _ hlt h.isMatch)
  · exact Std.not_lt.1 (fun hlt => h.not_isMatch _ hlt h'.isMatch)

open Classical in
theorem IsMatch.exists_isLongestMatch {pat : ρ} [ForwardPatternModel pat] {s : Slice} {pos : s.Pos} :
    IsMatch pat pos → ∃ (pos' : s.Pos), IsLongestMatch pat pos' := by
  induction pos using WellFounded.induction Pos.wellFounded_gt with | h pos ih
  intro h₁
  by_cases h₂ : ∃ pos', pos < pos' ∧ IsMatch pat pos'
  · obtain ⟨pos', hp₁, hp₂⟩ := h₂
    exact ih _ hp₁ hp₂
  · exact ⟨pos, ⟨h₁, fun p' hp₁ hp₂ => h₂ ⟨_, hp₁, hp₂⟩⟩⟩

theorem IsLongestMatch.le_of_isMatch {pat : ρ} [ForwardPatternModel pat] {s : Slice} {pos pos' : s.Pos}
    (h : IsLongestMatch pat pos) (h' : IsMatch pat pos') : pos' ≤ pos :=
  Std.not_lt.1 (fun hlt => h.not_isMatch _ hlt h')

/--
Predicate stating that a match for a given pattern is never a proper prefix of another match.

This implies that the notion of match and longest match coincide.
-/
class NoPrefixForwardPatternModel {ρ : Type} (pat : ρ) [ForwardPatternModel pat] : Prop where
  eq_empty (s t) : ForwardPatternModel.Matches pat s → ForwardPatternModel.Matches pat (s ++ t) → t = ""

theorem NoPrefixForwardPatternModel.of_length_toList_eq {ρ : Type} {pat : ρ} [ForwardPatternModel pat]
    (h : ∀ s t, ForwardPatternModel.Matches pat s → ForwardPatternModel.Matches pat t → s.toList.length = t.toList.length) :
    NoPrefixForwardPatternModel pat where
  eq_empty s t hs ht := by simpa using h s _ hs ht

theorem isLongestMatch_iff_isMatch {ρ : Type} (pat : ρ) [ForwardPatternModel pat] [NoPrefixForwardPatternModel pat]
    {s : Slice} {pos : s.Pos} : IsLongestMatch pat pos ↔ IsMatch pat pos := by
  refine ⟨fun h => h.isMatch, fun h => ⟨h, fun pos' hpos' hm => ?_⟩⟩
  obtain ⟨t₁, t₂, ht₁, ht₂⟩ := isMatch_iff_exists_splits.1 h
  obtain ⟨t₁', t₂', ht₁', ht₂'⟩ := isMatch_iff_exists_splits.1 hm
  obtain ⟨t₅, ht₅, ht₅', ht₅''⟩ := (ht₁.lt_iff_exists_eq_append ht₁').1 hpos'
  exact ht₅ (NoPrefixForwardPatternModel.eq_empty _ _ ht₂ (ht₅' ▸ ht₂'))

/--
Predicate stating that the slice formed by {name}`startPos` and {name}`endPos` contains is a match
of {name}`pat` in {name}`s` and it is longest among matches starting at {name}`startPos`.
-/
structure IsLongestMatchAt (pat : ρ) [ForwardPatternModel pat] {s : Slice} (startPos endPos : s.Pos) : Prop where
  le : startPos ≤ endPos
  isLongestMatch_sliceFrom : IsLongestMatch pat (Slice.Pos.sliceFrom _ _ le)

theorem isLongestMatchAt_iff {pat : ρ} [ForwardPatternModel pat] {s : Slice} {pos₁ pos₂ : s.Pos} :
    IsLongestMatchAt pat pos₁ pos₂ ↔
      ∃ (h : pos₁ ≤ pos₂), IsLongestMatch pat (Slice.Pos.sliceFrom _ _ h) :=
  ⟨fun ⟨h, h'⟩ => ⟨h, h'⟩, fun ⟨h, h'⟩ => ⟨h, h'⟩⟩

theorem IsLongestMatchAt.lt {pat : ρ} [ForwardPatternModel pat] {s : Slice} {startPos endPos : s.Pos}
    (h : IsLongestMatchAt pat startPos endPos) : startPos < endPos := by
  have := h.isLongestMatch_sliceFrom.ne_startPos
  rw [← Pos.startPos_lt_iff, ← Slice.Pos.ofSliceFrom_lt_ofSliceFrom_iff] at this
  simpa

theorem IsLongestMatchAt.eq {pat : ρ} [ForwardPatternModel pat] {s : Slice} {startPos endPos endPos' : s.Pos}
    (h : IsLongestMatchAt pat startPos endPos) (h' : IsLongestMatchAt pat startPos endPos') :
    endPos = endPos' := by
  simpa using h.isLongestMatch_sliceFrom.eq h'.isLongestMatch_sliceFrom

theorem IsLongestMatch.isLongestMatchAt_ofSliceFrom {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {p₀ : s.Pos} {pos : (s.sliceFrom p₀).Pos} (h : IsLongestMatch pat pos) :
    IsLongestMatchAt pat p₀ (Slice.Pos.ofSliceFrom pos) where
  le := Slice.Pos.le_ofSliceFrom
  isLongestMatch_sliceFrom := by simpa

/--
Predicate stating that there is a (longest) match starting at the given position.
-/
structure MatchesAt (pat : ρ) [ForwardPatternModel pat] {s : Slice} (pos : s.Pos) : Prop where
  exists_isLongestMatchAt : ∃ endPos, IsLongestMatchAt pat pos endPos

theorem matchesAt_iff_exists_isLongestMatchAt {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {pos : s.Pos} : MatchesAt pat pos ↔ ∃ endPos, IsLongestMatchAt pat pos endPos :=
  ⟨fun ⟨h⟩ => h, fun h => ⟨h⟩⟩

theorem matchesAt_iff_exists_isLongestMatch {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {pos : s.Pos} :
    MatchesAt pat pos ↔ ∃ (endPos : s.Pos), ∃ h, IsLongestMatch pat (pos.sliceFrom endPos h) :=
  ⟨fun ⟨p, h⟩ => ⟨p, h.le, h.isLongestMatch_sliceFrom⟩, fun ⟨p, h₁, h₂⟩ => ⟨p, ⟨h₁, h₂⟩⟩⟩

theorem matchesAt_iff_exists_isMatch {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {pos : s.Pos} :
    MatchesAt pat pos ↔ ∃ (endPos : s.Pos), ∃ h, IsMatch pat (pos.sliceFrom endPos h) := by
  refine ⟨fun ⟨p, h⟩ => ⟨p, h.le, h.isLongestMatch_sliceFrom.isMatch⟩, fun ⟨p, h₁, h₂⟩ => ?_⟩
  obtain ⟨q, hq⟩ := h₂.exists_isLongestMatch
  exact ⟨Pos.ofSliceFrom q,
    ⟨Std.le_trans h₁ (by simpa [← Pos.ofSliceFrom_le_ofSliceFrom_iff] using hq.le_of_isMatch h₂),
     by simpa using hq⟩⟩

open Classical in
/--
Noncomputable model function returning the end point of the longest match starting at the given
position, or {lean}`none` if there is no match.
-/
noncomputable def matchAt? {ρ : Type} (pat : ρ) [ForwardPatternModel pat]
    {s : Slice} (startPos : s.Pos) : Option s.Pos :=
  if h : ∃ endPos, IsLongestMatchAt pat startPos endPos then some h.choose else none

@[simp]
theorem matchAt?_eq_some_iff {ρ : Type} {pat : ρ} [ForwardPatternModel pat]
    {s : Slice} {startPos endPos : s.Pos} :
    matchAt? pat startPos = some endPos ↔ IsLongestMatchAt pat startPos endPos := by
  fun_cases matchAt? with
  | case1 h => simpa using ⟨by rintro rfl; exact h.choose_spec, fun h' => h.choose_spec.eq h'⟩
  | case2 => simp_all

@[simp]
theorem matchAt?_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPatternModel pat]
    {s : Slice} {startPos : s.Pos} :
    matchAt? pat startPos = none ↔ ¬ MatchesAt pat startPos := by
  fun_cases matchAt? with
  | case1 h => simpa using ⟨h⟩
  | case2 h => simpa using fun ⟨h'⟩ => h h'

/--
Predicate stating compatibility between {name}`ForwardPatternModel` and {name}`ForwardPattern`.

This extends {name}`LawfulForwardPattern`, but it is much stronger because it forces the
{name}`ForwardPattern` to match the longest prefix of the given slice that matches the property
supplied by the {name}`ForwardPatternModel` instance.
-/
class LawfulForwardPatternModel {ρ : Type} (pat : ρ) [ForwardPattern pat]
    [ForwardPatternModel pat] : Prop extends LawfulForwardPattern pat where
  dropPrefix?_eq_some_iff (pos) : ForwardPattern.dropPrefix? pat s = some pos ↔ IsLongestMatch pat pos

open Classical in
theorem LawfulForwardPatternModel.dropPrefix?_eq_none_iff {ρ : Type} {pat : ρ} [ForwardPattern pat] [ForwardPatternModel pat]
    [LawfulForwardPatternModel pat] {s : Slice} {p₀ : s.Pos} :
    ForwardPattern.dropPrefix? pat (s.sliceFrom p₀) = none ↔ ¬ MatchesAt pat p₀ := by
  rw [← Decidable.not_iff_not]
  simp [Option.ne_none_iff_exists', LawfulForwardPatternModel.dropPrefix?_eq_some_iff]
  refine ⟨fun ⟨p, hp⟩ => ?_, fun ⟨p, hp⟩ => ?_⟩
  · exact ⟨Slice.Pos.ofSliceFrom p, hp.isLongestMatchAt_ofSliceFrom⟩
  · exact ⟨p₀.sliceFrom p hp.le, hp.isLongestMatch_sliceFrom⟩

/--
Inductive predicate stating that a list of search steps represents a valid search from a given
position in a slice.

"Searching" here means always taking the longest match at the first position where the pattern
matches.

Hence, this predicate determines the list of search steps up to grouping of rejections.
-/
inductive IsValidSearchFrom (pat : ρ) [ForwardPatternModel pat] {s : Slice} :
    s.Pos → List (SearchStep s) → Prop where
  | endPos : IsValidSearchFrom pat s.endPos []
  | matched {startPos endPos : s.Pos} :
      IsLongestMatchAt pat startPos endPos → IsValidSearchFrom pat endPos l →
      IsValidSearchFrom pat startPos (.matched startPos endPos :: l)
  | mismatched {startPos endPos : s.Pos} : startPos < endPos →
      (∀ pos, startPos ≤ pos → pos < endPos → ¬ MatchesAt pat pos) →
      IsValidSearchFrom pat endPos l → IsValidSearchFrom pat startPos (.rejected startPos endPos :: l)

theorem IsValidSearchFrom.matched_of_eq {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {startPos startPos' endPos : s.Pos} {l : List (SearchStep s)} (h₁ : IsValidSearchFrom pat endPos l)
    (h₂ : IsLongestMatchAt pat startPos' endPos)
    (h₃ : startPos = startPos') : IsValidSearchFrom pat startPos' (.matched startPos endPos :: l) := by
  cases h₃
  exact IsValidSearchFrom.matched h₂ h₁

theorem IsValidSearchFrom.mismatched_of_eq {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {startPos startPos' endPos : s.Pos} {l : List (SearchStep s)} (h₁ : IsValidSearchFrom pat endPos l)
      (h₀ : startPos' < endPos)
      (h₂ : ∀ pos, startPos' ≤ pos → pos < endPos → ¬ MatchesAt pat pos) (h₃ : startPos = startPos') :
      IsValidSearchFrom pat startPos' (.rejected startPos endPos :: l) := by
  cases h₃
  exact IsValidSearchFrom.mismatched h₀ h₂ h₁

theorem IsValidSearchFrom.endPos_of_eq {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {p : s.Pos} {l : List (SearchStep s)} (hp : p = s.endPos) (hl : l = []) :
    IsValidSearchFrom pat p l := by
  cases hp
  cases hl
  exact IsValidSearchFrom.endPos

/--
Predicate stating compatibility between {name}`ForwardPatternModel` and {name}`ToForwardSearcher`.

We require the searcher to always match the longest match at the first position where the pattern
matches; see {name}`IsValidSearchFrom`.
-/
class LawfulToForwardSearcherModel {ρ : Type} (pat : ρ) [ForwardPatternModel pat] {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] : Prop where
  isValidSearchFrom_toList (s) : IsValidSearchFrom pat s.startPos (ToForwardSearcher.toSearcher pat s).toList

set_option backward.isDefEq.respectTransparency false in
theorem LawfulToForwardSearcherModel.defaultImplementation {pat : ρ} [ForwardPattern pat] [StrictForwardPattern pat]
    [ForwardPatternModel pat] [LawfulForwardPatternModel pat] :
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
        · rw [LawfulForwardPattern.dropPrefixOfNonempty?_eq,
            LawfulForwardPatternModel.dropPrefix?_eq_some_iff] at heq'
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
        rwa [LawfulForwardPattern.dropPrefixOfNonempty?_eq,
          LawfulForwardPatternModel.dropPrefix?_eq_none_iff] at heq'
    · split at heq <;> simp at heq
    · split at heq <;> simp at heq

end String.Slice.Pattern.Model
