/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Markus Himmel
-/
module

prelude
public import Init.Data.String.Lemmas.Pattern.Basic
public import Init.Data.String.Slice
public import Init.Data.String.Search
import all Init.Data.String.Slice
import all Init.Data.String.Search
import Init.Data.Option.Lemmas
import Init.Data.String.Termination
import Init.Data.String.Lemmas.Order
import Init.ByCases
import Init.Data.Order.Lemmas
import Init.Data.String.OrderInstances
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.Iterators.Lemmas.Combinators.FilterMap
import Init.Data.String.Lemmas.IsEmpty

set_option doc.verso true

/-!
# Verification of {name}`String.Slice.splitToSubslice`

This PR verifies the {name}`String.Slice.splitToSubslice` function by relating it to a model
implementation based on the {name}`String.Slice.Pattern.Model.PatternModel` class.

This gives a low-level correctness proof from which higher-level API lemmas can be derived.
-/

namespace String.Slice.Pattern.Model

@[cbv_opaque]
public protected noncomputable def split {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    (firstRejected curr : s.Pos) (hle : firstRejected ≤ curr) : List s.Subslice :=
  if h : curr = s.endPos then
    [s.subslice _ _ hle]
  else
    match hd : matchAt? pat curr with
    | some pos =>
      have : curr < pos := (matchAt?_eq_some_iff.1 hd).lt
      s.subslice _ _ hle :: Model.split pat pos pos (Std.le_refl _)
    | none => Model.split pat firstRejected (curr.next h) (Std.le_trans hle (by simp))
termination_by curr

@[simp]
public theorem split_endPos {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat] {s : Slice}
    {firstRejected : s.Pos} :
    Model.split (s := s) pat firstRejected s.endPos (by simp) = [s.subslice firstRejected s.endPos (by simp)] := by
  simp [Model.split]

public theorem split_eq_of_isLongestMatchAt {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    {s : Slice} {firstRejected start stop : s.Pos} {hle} (h : IsLongestMatchAt pat start stop) :
    Model.split pat firstRejected start hle =
      s.subslice _ _ hle :: Model.split pat stop stop (by exact Std.le_refl _) := by
  rw [Model.split, dif_neg (Slice.Pos.ne_endPos_of_lt h.lt)]
  split
  · congr <;> exact (matchAt?_eq_some_iff.1 ‹_›).eq h
  · simp [matchAt?_eq_some_iff.2 ‹_›] at *

public theorem split_eq_of_not_matchesAt {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    {s : Slice} {firstRejected start} (stop : s.Pos) (h₀ : start ≤ stop) {hle}
    (h : ∀ p, start ≤ p → p < stop → ¬ MatchesAt pat p) :
    Model.split pat firstRejected start hle =
      Model.split pat firstRejected stop (by exact Std.le_trans hle h₀) := by
  induction start using WellFounded.induction Slice.Pos.wellFounded_gt with | h start ih
  by_cases h' : start < stop
  · rw [Model.split, dif_neg (Slice.Pos.ne_endPos_of_lt h')]
    have : ¬ MatchesAt pat start := h start (Slice.Pos.le_refl _) h'
    split
    · rename_i heq
      simp [matchAt?_eq_none_iff.2 ‹_›] at heq
    · rw [ih _ (by simp) (by simpa)]
      exact fun p hp₁ hp₂ => h p (Std.le_of_lt (by simpa using hp₁)) hp₂
  · obtain rfl : start = stop := Std.le_antisymm h₀ (Std.not_lt.1 h')
    simp

public theorem split_eq_next_of_not_matchesAt {ρ : Type} {pat : ρ} [PatternModel pat] [StrictPatternModel pat]
    {s : Slice} {firstRejected start} {hle} (hs : start ≠ s.endPos) (h : ¬ MatchesAt pat start) :
    Model.split pat firstRejected start hle =
      Model.split pat firstRejected (start.next hs) (by exact Std.le_trans hle (by simp)) := by
  refine split_eq_of_not_matchesAt _ (by simp) (fun p hp₁ hp₂ => ?_)
  obtain rfl : start = p := Std.le_antisymm hp₁ (by simpa using hp₂)
  exact h

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
    [PatternModel pat] [StrictPatternModel pat] (l : List (SearchStep s)) (pos pos' : s.Pos) (h₀ : pos ≤ pos')
    (h' : ∀ p, pos ≤ p → p < pos' → ¬ MatchesAt pat p)
    (h : IsValidSearchFrom pat pos' l) :
    splitFromSteps pos l = Model.split pat pos pos' h₀ := by
  induction h generalizing pos with
  | endPos =>
    simp [splitFromSteps]
  | matched h valid ih =>
    simp only [splitFromSteps]
    rw [subslice!_eq_subslice h₀, split_eq_of_isLongestMatchAt h, ih]
    simp +contextual [← Std.not_lt]
  | mismatched h rej valid ih =>
    simp only [splitFromSteps]
    rename_i l startPos endPos
    rw [split_eq_of_not_matchesAt _ (Std.le_of_lt h) rej, ih]
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

@[cbv_eval]
public theorem toList_splitToSubslice_eq_modelSplit {ρ : Type} (pat : ρ) [PatternModel pat] [StrictPatternModel pat]
    {σ : Slice → Type} [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] [LawfulToForwardSearcherModel pat] (s : Slice) :
    (s.splitToSubslice pat).toList = Model.split pat s.startPos s.startPos (by exact Std.le_refl _) := by
  rw [toList_splitToSubslice_eq_splitFromSteps, IsValidSearchFrom.splitFromSteps_eq_extend_split pat _
    s.startPos s.startPos (Std.le_refl _) _ (LawfulToForwardSearcherModel.isValidSearchFrom_toList _)]
  simp

end Pattern

open Pattern

public theorem toList_splitToSubslice_of_isEmpty {ρ : Type} (pat : ρ)
    [Model.PatternModel pat] [Model.StrictPatternModel pat] {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] [Model.LawfulToForwardSearcherModel pat] {s : Slice}
    (h : s.isEmpty = true) :
    (s.splitToSubslice pat).toList = [s.subsliceFrom s.endPos] := by
  simp [toList_splitToSubslice_eq_modelSplit, Slice.startPos_eq_endPos_iff.2 h]

public theorem toList_split_eq_splitToSubslice {ρ : Type} (pat : ρ) {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] {s : Slice} :
    (s.split pat).toList = (s.splitToSubslice pat).toList.map Subslice.toSlice := by
  simp [split, Std.Iter.toList_map]

public theorem toList_split_of_isEmpty {ρ : Type} (pat : ρ)
    [Model.PatternModel pat] [Model.StrictPatternModel pat] {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] [Model.LawfulToForwardSearcherModel pat] {s : Slice}
    (h : s.isEmpty = true) :
    (s.split pat).toList.map Slice.copy = [""] := by
  rw [toList_split_eq_splitToSubslice, toList_splitToSubslice_of_isEmpty _ h]
  simp

end Slice

open Slice.Pattern

public theorem split_eq_split_toSlice {ρ : Type} {pat : ρ} {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)] {s : String} :
  s.split pat = s.toSlice.split pat := (rfl)

@[simp]
public theorem toList_split_empty {ρ : Type} (pat : ρ)
    [Model.PatternModel pat] [Model.StrictPatternModel pat] {σ : Slice → Type}
    [ToForwardSearcher pat σ] [∀ s, Std.Iterator (σ s) Id (SearchStep s)]
    [∀ s, Std.Iterators.Finite (σ s) Id] [Model.LawfulToForwardSearcherModel pat] :
    ("".split pat).toList.map Slice.copy = [""] := by
  rw [split_eq_split_toSlice, Slice.toList_split_of_isEmpty _ (by simp)]

end String
