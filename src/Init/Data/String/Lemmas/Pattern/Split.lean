/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Lemmas.Pattern.Basic
public import Init.Data.String.Slice
import all Init.Data.String.Slice
import Init.Data.Option.Lemmas
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Order
import Init.ByCases
import Init.Data.Order.Lemmas
import Init.Data.String.OrderInstances
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Collect

set_option doc.verso true

/-!
# Verification of {name}`String.Slice.splitToSubslice`

This PR verifies the {name}`String.Slice.splitToSubslice` function by relating it to a model
implementation based on the {name}`String.Slice.Pattern.Model.ForwardPatternModel` class.

This gives a low-level correctness proof from which higher-level API lemmas can be derived.
-/

namespace String.Slice.Pattern.Model

/--
Represents a list of subslices of a slice {name}`s`, the first of which starts at the given
position {name}`startPos`. This is a natural type for a split routine to return.
-/
@[ext]
public structure SlicesFrom {s : Slice} (startPos : s.Pos) : Type where
  l : List s.Subslice
  any_head? : l.head?.any (·.startInclusive = startPos)

namespace SlicesFrom

/--
A {name}`SlicesFrom` consisting of a single empty subslice at the position {name}`pos`.
-/
public def «at» {s : Slice} (pos : s.Pos) : SlicesFrom pos where
  l := [s.subslice pos pos (Slice.Pos.le_refl _)]
  any_head? := by simp

@[simp]
public theorem l_at {s : Slice} (pos : s.Pos) :
    (SlicesFrom.at pos).l = [s.subslice pos pos (Slice.Pos.le_refl _)] := (rfl)

/--
Concatenating two {name}`SlicesFrom` yields a {name}`SlicesFrom` from the first position.
-/
public def append {s : Slice} {p₁ p₂ : s.Pos} (l₁ : SlicesFrom p₁) (l₂ : SlicesFrom p₂) :
    SlicesFrom p₁ where
  l := l₁.l ++ l₂.l
  any_head? := by simpa using Option.any_or_of_any_left l₁.any_head?

@[simp]
public theorem l_append {s : Slice} {p₁ p₂ : s.Pos} {l₁ : SlicesFrom p₁} {l₂ : SlicesFrom p₂} :
    (l₁.append l₂).l = l₁.l ++ l₂.l :=
  (rfl)

/--
Given a {lean}`SlicesFrom p₂` and a position {name}`p₁` such that {lean}`p₁ ≤ p₂`, obtain a
{lean}`SlicesFrom p₁` by extending the left end of the first subslice to from {name}`p₂` to
{name}`p₁`.
-/
public def extend {s : Slice} (p₁ : s.Pos) {p₂ : s.Pos} (h : p₁ ≤ p₂) (l : SlicesFrom p₂) :
    SlicesFrom p₁ where
  l :=
    match l.l, l.any_head? with
    | st :: sts, h => st.extendLeft p₁ (by simp_all) :: sts
  any_head? := by split; simp

@[simp]
public theorem l_extend {s : Slice} {p₁ p₂ : s.Pos} (h : p₁ ≤ p₂) {l : SlicesFrom p₂} :
    (l.extend p₁ h).l =
    match l.l, l.any_head? with
    | st :: sts, h => st.extendLeft p₁ (by simp_all) :: sts :=
  (rfl)

@[simp]
public theorem extend_self {s : Slice} {p₁ : s.Pos} (l : SlicesFrom p₁) :
    l.extend p₁ (Slice.Pos.le_refl _) = l := by
  rcases l with ⟨l, h⟩
  match l, h with
  | st :: sts, h =>
    simp at h
    simp [SlicesFrom.extend, ← h]

@[simp]
public theorem extend_extend {s : Slice} {p₀ p₁ p₂ : s.Pos} {h : p₀ ≤ p₁} {h' : p₁ ≤ p₂}
    {l : SlicesFrom p₂} : (l.extend p₁ h').extend p₀ h = l.extend p₀ (Slice.Pos.le_trans h h') := by
  rcases l with ⟨l, h⟩
  match l, h with
  | st :: sts, h => simp [SlicesFrom.extend]

end SlicesFrom

/--
Noncomputable model implementation of {name}`String.Slice.splitToSubslice` based on
{name}`ForwardPatternModel`. This is supposed to be simple enough to allow deriving higher-level
API lemmas about the public splitting functions.
-/
public protected noncomputable def split {ρ : Type} (pat : ρ) [ForwardPatternModel pat] {s : Slice}
    (start : s.Pos) : SlicesFrom start :=
  if h : start = s.endPos then
    .at start
  else
    match hd : matchAt? pat start with
    | some pos =>
      have : start < pos := (matchAt?_eq_some_iff.1 hd).lt
      (SlicesFrom.at start).append (Model.split pat pos)
    | none => (Model.split pat (start.next h)).extend start (by simp)
termination_by start

@[simp]
public theorem split_endPos {ρ : Type} {pat : ρ} [ForwardPatternModel pat] {s : Slice} :
    Model.split pat s.endPos = SlicesFrom.at s.endPos := by
  simp [Model.split]

public theorem split_eq_of_isLongestMatchAt {ρ : Type} {pat : ρ} [ForwardPatternModel pat]
    {s : Slice} {start stop : s.Pos} (h : IsLongestMatchAt pat start stop) :
    Model.split pat start = (SlicesFrom.at start).append (Model.split pat stop) := by
  rw [Model.split, dif_neg (Slice.Pos.ne_endPos_of_lt h.lt)]
  split
  · congr <;> exact (matchAt?_eq_some_iff.1 ‹_›).eq h
  · simp [matchAt?_eq_some_iff.2 ‹_›] at *

public theorem split_eq_of_not_matchesAt {ρ : Type} {pat : ρ} [ForwardPatternModel pat] {s : Slice}
    {start stop : s.Pos} (h₀ : start ≤ stop) (h : ∀ p, start ≤ p → p < stop → ¬ MatchesAt pat p) :
    Model.split pat start = (SlicesFrom.extend start h₀ (Model.split pat stop)) := by
  induction start using WellFounded.induction Slice.Pos.wellFounded_gt with | h start ih
  by_cases h' : start < stop
  · rw [Model.split, dif_neg (Slice.Pos.ne_endPos_of_lt h')]
    have : ¬ MatchesAt pat start := h start (Slice.Pos.le_refl _) h'
    split
    · rename_i heq
      simp [matchAt?_eq_none_iff.2 ‹_›] at heq
    · rw [ih, SlicesFrom.extend_extend]
      · simp
      · simp [h']
      · refine fun p hp₁ hp₂ => h p (Std.le_of_lt (by simpa using hp₁)) hp₂
  · obtain rfl : start = stop := Std.le_antisymm h₀ (Std.not_lt.1 h')
    simp

/--
Splits a slice {name}`s` into subslices from a list of {lean}`SearchStep s`.

This is an intermediate step in the verification. The equivalence of
{name}`String.Slice.splitToSubslice` and {name}`splitFromSteps` is pure "iteratorology", while
the equivalence of {name}`splitFromSteps` and {name}`split` is the actual correctness proof for the
splitting routine.
-/
def splitFromSteps {s : Slice} (currPos : s.Pos) (l : List (SearchStep s)) : List s.Subslice :=
  match l with
  | [] => [s.subsliceFrom currPos]
  | .rejected .. :: l => splitFromSteps currPos l
  | .matched p q :: l => s.subslice! currPos p :: splitFromSteps q l

theorem IsValidSearchFrom.splitFromSteps_eq_extend_split {ρ : Type} (pat : ρ)
    [ForwardPatternModel pat] (l : List (SearchStep s)) (pos pos' : s.Pos) (h₀ : pos ≤ pos')
    (h' : ∀ p, pos ≤ p → p < pos' → ¬ MatchesAt pat p)
    (h : IsValidSearchFrom pat pos' l) :
    splitFromSteps pos l = ((Model.split pat pos').extend pos h₀).l := by
  induction h generalizing pos with
  | endPos =>
    simp only [splitFromSteps, Model.split, ↓reduceDIte, SlicesFrom.l_extend, List.head?_cons,
      Option.any_some]
    split
    simp_all only [SlicesFrom.l_at, List.cons.injEq, List.nil_eq, List.head?_cons, Option.any_some,
      decide_eq_true_eq, heq_eq_eq, and_true]
    rename_i h
    simp only [← h.1]
    ext <;> simp
  | matched h valid ih =>
    simp only [splitFromSteps]
    rw [subslice!_eq_subslice h₀, split_eq_of_isLongestMatchAt h]
    simp only [SlicesFrom.append, SlicesFrom.at, List.cons_append, List.nil_append,
      SlicesFrom.l_extend, List.cons.injEq]
    refine ⟨?_, ?_⟩
    · ext <;> simp
    · rw [ih _ (Slice.Pos.le_refl _), SlicesFrom.extend_self]
      exact fun p hp₁ hp₂ => False.elim (Std.lt_irrefl (Std.lt_of_le_of_lt hp₁ hp₂))
  | mismatched h rej valid ih =>
    simp only [splitFromSteps]
    rename_i l startPos endPos
    rw [split_eq_of_not_matchesAt (Std.le_of_lt h) rej, SlicesFrom.extend_extend, ih]
    intro p hp₁ hp₂
    by_cases hp : p < startPos
    · exact h' p hp₁ hp
    · exact rej _ (Std.not_lt.1 hp) hp₂

theorem SplitIterator.toList_eq_splitFromSteps {ρ : Type} {pat : ρ} {σ : Slice → Type}
    [ToForwardSearcher pat σ]
    [∀ s, Std.Iterator (σ s) Id (SearchStep s)] [∀ s, Std.Iterators.Finite (σ s) Id] {s : Slice}
    (it : Std.Iter (α := σ s) (SearchStep s)) (currPos : s.Pos) :
    (Std.Iter.mk (α := SplitIterator pat s) (.operating currPos it)).toList =
      splitFromSteps currPos it.toList := by
  induction it using Std.Iter.inductSteps generalizing currPos with | step it ihy ihs
  rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
  conv => rhs; rw [Std.Iter.toList_eq_match_step]
  simp only [Std.Iter.toIterM_mk]
  cases it.step using Std.PlausibleIterStep.casesOn with
  | yield it out h =>
    match out with
    | .matched startPos endPos => simp [splitFromSteps, ← ihy h]
    | .rejected startPos endPos => simp [splitFromSteps, ← ihy h]
  | skip it h => simp [← ihs h]
  | done =>
    simp only [Id.run_pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure_yield,
      Std.PlausibleIterStep.yield, Std.IterM.toIter_mk, splitFromSteps, List.cons.injEq, true_and]
    rw [Std.Iter.toList_eq_match_step, Std.Iter.step_eq]
    simp

theorem toList_splitToSubslice_eq_splitFromSteps {ρ : Type} {pat : ρ} {σ : Slice → Type} [ToForwardSearcher pat σ]
    [∀ s, Std.Iterator (σ s) Id (SearchStep s)] [∀ s, Std.Iterators.Finite (σ s) Id] (s : Slice) :
    (s.splitToSubslice pat).toList = splitFromSteps s.startPos (ToForwardSearcher.toSearcher pat s).toList := by
  rw [splitToSubslice, SplitIterator.toList_eq_splitFromSteps]

end Model

open Model

public theorem toList_splitToSubslice_eq_modelSplit {ρ : Type} (pat : ρ) [ForwardPatternModel pat]
    {σ : Slice → Type} [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] [LawfulToForwardSearcherModel pat] (s : Slice) :
    (s.splitToSubslice pat).toList = (Model.split pat s.startPos).l := by
  rw [toList_splitToSubslice_eq_splitFromSteps, IsValidSearchFrom.splitFromSteps_eq_extend_split pat _
    s.startPos s.startPos (Std.le_refl _) _ (LawfulToForwardSearcherModel.isValidSearchFrom_toList _),
    SlicesFrom.extend_self]
  simp

end String.Slice.Pattern
