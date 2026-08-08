/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Consumers.Access
public import Init.Data.Iterators.Consumers.Monadic.Access
public import Init.Data.Iterators.Consumers.Collect
public import Init.Data.Iterators.Consumers.Loop
public import Init.Data.Iterators.Combinators.Take
public import Std.Data.Iterators.Combinators.StepSize
import all Std.Data.Iterators.Combinators.StepSize
import Std.Data.Iterators.Lemmas.Combinators.Monadic.StepSize
import Init.Data.Iterators.Lemmas.Consumers.Access
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Access
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Access
import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop
import all Init.Data.Iterators.Consumers.Monadic.Access
import Init.Data.Iterators.Lemmas.Basic
import Init.Data.Iterators.Lemmas.Monadic.Basic
import Init.Omega

public section
open Std Std.Iterators Std.Iterators.Types

namespace Std.Iter

theorem stepSize_eq_intermediateStepSize [Iterator α Id β] [IteratorAccess α Id]
    {it : Iter (α := α) β} {n : Nat} :
    it.stepSize n = Intermediate.stepSize it 0 n :=
  rfl

theorem nextAtIdxSlow?_zero_intermediate_stepSize [Iterator α Id β] [Productive α Id]
    [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {i n : Nat} :
    (Intermediate.stepSize it i n).nextAtIdxSlow? 0 =
      match it.nextAtIdxSlow? i with
      | .yield it' out h =>
        .yield (Intermediate.stepSize it' (n - 1) n) out (by
          refine .zero_yield ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
            Intermediate.stepSize, IterM.Intermediate.stepSize, StepSizeIterator.instIterator]) -- TODO: remove `inst...` argument as soon as possible
      | .skip it' h => IterM.not_isPlausibleNthOutputStep_skip.elim h
      | .done h =>
        .done (by
          refine .done ?_
          simpa [IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
            Intermediate.stepSize, IterM.Intermediate.stepSize, StepSizeIterator.instIterator]) := by -- TODO: remove `inst...` argument as soon as possible
  simp only [Iter.nextAtIdxSlow?, Intermediate.stepSize, toIterM_toIter,
    IterM.nextAtIdxSlow?_stepSize_aux, Id.run_bind]
  apply Subtype.ext
  let step := (it.toIterM.nextAtIdxSlow? i).run
  cases hs : step using PlausibleIterStep.casesOn
  · simp [hs, step]
  · exact IterM.not_isPlausibleNthOutputStep_skip.elim ‹_›
  · simp [hs, step]

private theorem atIdxSlow?_eq_of_nextAtIdxSlow? [Iterator α Id β] [Productive α Id]
    {it : Iter (α := α) β} {i : Nat} :
    it.atIdxSlow? i = match (it.nextAtIdxSlow? i).val with
    | .yield _ out => some out
    | .skip _ => none
    | .done => none := by
  induction i, it using Iter.atIdxSlow?.induct_unfolding <;>
    (rw [nextAtIdxSlow?_eq_match]; simp [*])

private theorem atIdxSlow?_none_of_nextAtIdxSlow?_eq_done [Iterator α Id β] [Productive α Id]
    {it : Iter (α := α) β} {i j : Nat}
    (h : (it.nextAtIdxSlow? i).val = .done) (hij : i ≤ j) :
    it.atIdxSlow? j = none := by
  induction j generalizing it i with
  | zero =>
    cases show i = 0 from Nat.le_antisymm hij (Nat.zero_le _)
    rw [atIdxSlow?_eq_of_nextAtIdxSlow?, h]
  | succ j ih =>
    induction it using Iter.inductSkips with | step it ih_skip
    rw [atIdxSlow?_eq_match]
    cases hstep : it.step using PlausibleIterStep.casesOn with
    | yield it' out hp =>
      rw [nextAtIdxSlow?_eq_match] at h
      simp only [hstep, PlausibleIterStep.yield] at h
      cases i with
      | zero => cases h
      | succ i => exact ih h (Nat.le_of_succ_le_succ hij)
    | skip it' hp =>
      rw [nextAtIdxSlow?_eq_match] at h
      simp only [hstep] at h
      exact ih_skip hp h
    | done hp => simp

private theorem atIdxSlow?_succ_of_nextAtIdxSlow?_eq_yield [Iterator α Id β] [Productive α Id]
    {it it' : Iter (α := α) β} {i j : Nat} {out : β}
    (h : (it.nextAtIdxSlow? i).val = .yield it' out) :
    it.atIdxSlow? (i + 1 + j) = it'.atIdxSlow? j := by
  induction i, it using Iter.atIdxSlow?.induct_unfolding generalizing j with
  | yield_zero it it'' out' hp hs =>
    rw [nextAtIdxSlow?_eq_match] at h
    simp only [hs, PlausibleIterStep.yield, IterStep.yield.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    show atIdxSlow? (0 + 1 + j) it = atIdxSlow? j it''
    rw [show (0 : Nat) + 1 + j = j + 1 from by omega, atIdxSlow?_eq_match]
    simp [hs]
  | yield_succ it it'' out' hp hs k ih =>
    rw [nextAtIdxSlow?_eq_match, Nat.succ_eq_add_one, hs] at h
    rw [show k + 1 + 1 + j = (k + 1 + j) + 1 from by omega, atIdxSlow?_eq_match]
    simpa [hs] using ih h
  | skip_case n it it'' hp hs ih =>
    rw [nextAtIdxSlow?_eq_match, hs] at h
    rw [atIdxSlow?_eq_match, hs]
    simpa using ih h
  | done_case n it hp hs =>
    rw [nextAtIdxSlow?_eq_match] at h; simp [hs] at h

private theorem nextAtIdxSlow?_zero_intermediate_stepSize_val [Iterator α Id β] [Productive α Id]
    [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {i n : Nat} :
    ((Intermediate.stepSize it i n).nextAtIdxSlow? 0).val =
      (it.nextAtIdxSlow? i).val.mapIterator (fun it' => Intermediate.stepSize it' (n - 1) n) := by
  have h := congrArg Subtype.val (nextAtIdxSlow?_zero_intermediate_stepSize (it := it) (i := i) (n := n))
  simp only at h
  rw [h]
  cases (it.nextAtIdxSlow? i) using PlausibleIterStep.casesOn with
  | yield => simp [IterStep.mapIterator]
  | skip _ h => exact IterM.not_isPlausibleNthOutputStep_skip.elim h
  | done => simp [IterStep.mapIterator]

theorem atIdxSlow?_intermediate_stepSize {α β} [Iterator α Id β] [Productive α Id]
    [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {i k n : Nat} :
    (Intermediate.stepSize it i n).atIdxSlow? k = it.atIdxSlow? (i + (n - 1 + 1) * k) := by
  induction k generalizing it i with
  | zero =>
    simp only [Nat.mul_zero, Nat.add_zero]
    rw [atIdxSlow?_eq_of_nextAtIdxSlow?, nextAtIdxSlow?_zero_intermediate_stepSize_val]
    rw [atIdxSlow?_eq_of_nextAtIdxSlow?]
    cases (it.nextAtIdxSlow? i).val with
    | yield => simp [IterStep.mapIterator]
    | skip => simp [IterStep.mapIterator]
    | done => simp [IterStep.mapIterator]
  | succ k ih =>
    cases hstep : (it.nextAtIdxSlow? i).val with
    | yield it' out =>
      have h_nextAtIdxSlow?_zero :
          ((Intermediate.stepSize it i n).nextAtIdxSlow? 0).val =
            .yield (Intermediate.stepSize it' (n - 1) n) out := by
        rw [nextAtIdxSlow?_zero_intermediate_stepSize_val, hstep, IterStep.mapIterator]
      have h_atIdxSlow?_succ : (Intermediate.stepSize it i n).atIdxSlow? (k + 1) =
          (Intermediate.stepSize it' (n - 1) n).atIdxSlow? k := by
        rw [show k + 1 = 0 + 1 + k by omega, ← atIdxSlow?_succ_of_nextAtIdxSlow?_eq_yield h_nextAtIdxSlow?_zero]
      rw [h_atIdxSlow?_succ, ih, ← atIdxSlow?_succ_of_nextAtIdxSlow?_eq_yield hstep]
      congr 1
      rw [Nat.mul_add]
      omega
    | skip it' =>
      exact IterM.not_isPlausibleNthOutputStep_skip.elim
        (by simpa [hstep] using (it.nextAtIdxSlow? i).property)
    | done =>
      have h_nextAtIdxSlow?_zero :
          ((Intermediate.stepSize it i n).nextAtIdxSlow? 0).val = .done := by
        rw [nextAtIdxSlow?_zero_intermediate_stepSize_val, hstep]; rfl
      rw [atIdxSlow?_none_of_nextAtIdxSlow?_eq_done h_nextAtIdxSlow?_zero (by omega)]
      exact (atIdxSlow?_none_of_nextAtIdxSlow?_eq_done hstep (by omega)).symm

theorem atIdxSlow?_stepSize [Iterator α Id β] [Productive α Id]
    [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {k n : Nat} :
    (it.stepSize n).atIdxSlow? k = it.atIdxSlow? ((n - 1 + 1) * k) := by
  simp [stepSize_eq_intermediateStepSize, atIdxSlow?_intermediate_stepSize]

theorem getElem?_toList_stepSize [Iterator α Id β]
    [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] [Finite α Id]
    {it : Iter (α := α) β} {k n : Nat} :
    (it.stepSize n).toList[k]? = it.toList[(n - 1 + 1) * k]? := by
  simp only [getElem?_toList_eq_atIdxSlow?, atIdxSlow?_stepSize]

theorem getElem?_toArray_stepSize [Iterator α Id β]
    [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] [Finite α Id]
    {it : Iter (α := α) β} {k n : Nat} :
    (it.stepSize n).toArray[k]? = it.toArray[(n - 1 + 1) * k]? := by
  simp only [← Array.getElem?_toList, Iter.toList_toArray, getElem?_toList_stepSize]

private theorem val_nextAtIdxSlow?_zero_eq_val_step [Iterator α Id β] [Productive α Id]
    {it : Iter (α := α) β} :
    (∀ (it' : Iter (α := α) β), ¬ it.IsPlausibleStep (.skip it')) →
    it.step.val = (it.nextAtIdxSlow? 0).val := by
  intro hno_skip
  rw [nextAtIdxSlow?_eq_match]
  cases it.step using PlausibleIterStep.casesOn with
  | yield => simp
  | skip _ hp => exact (hno_skip _).elim hp
  | done => simp

private theorem not_isPlausibleStep_skip_intermediateStepSize [Iterator α Id β]
    [IteratorAccess α Id] {it : Iter (α := α) β} {i n : Nat}
    {it' : Iter (α := Types.StepSizeIterator α Id β) β} :
    ¬ (Intermediate.stepSize it i n).IsPlausibleStep (.skip it') := by
  simp only [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep,
    IterStep.mapIterator, Intermediate.stepSize, IterM.Intermediate.stepSize]
  exact fun h => IterM.not_isPlausibleNthOutputStep_skip.elim h.1

private theorem val_step_intermediateStepSize [Iterator α Id β] [Productive α Id]
    [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] {it : Iter (α := α) β} {i n : Nat} :
    (Intermediate.stepSize it i n).step.val =
      (it.nextAtIdxSlow? i).val.mapIterator (fun it' => Intermediate.stepSize it' (n - 1) n) := by
  rw [val_nextAtIdxSlow?_zero_eq_val_step (fun _ => not_isPlausibleStep_skip_intermediateStepSize),
    nextAtIdxSlow?_zero_intermediate_stepSize_val]

theorem Intermediate.length_stepSize [Iterator α Id β] [Finite α Id]
    [Productive α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {it : Iter (α := α) β} {i n : Nat} :
    (Intermediate.stepSize it i n).length = (it.length + (n - 1) - i) / (n - 1 + 1) := by
  generalize hsit : Intermediate.stepSize it i n = sit
  replace hsit := hsit.symm
  induction sit using Iter.inductSteps generalizing it i with | step it ihy ihs
  rw [Std.Iter.length_eq_match_step]
  subst hsit
  rw [val_step_intermediateStepSize]
  cases h : (it.nextAtIdxSlow? i) using PlausibleIterStep.casesOn with
  | yield it' out hp =>
    simp only [IterStep.mapIterator]
    rw [ihy (it := it') (i := n - 1) (out := out) _ rfl]
    · have hlength := length_nextAtIdxSlow? (it := it) (n := i)
      simp only [h, IterStep.successor_yield, Option.elim] at hlength
      simp only [hlength, Nat.add_sub_cancel, Nat.zero_lt_succ, ← Nat.add_div_right]
      have hi := lt_length_of_nextAtIdxSlow?_eq_yield (by rw [h])
      congr 1; omega
    · have := (Intermediate.stepSize it i n).step.property
      simpa [val_step_intermediateStepSize, h, IterStep.mapIterator]
  | skip _ hp => exact IterM.not_isPlausibleNthOutputStep_skip.elim hp
  | done hp =>
    simp only [IterStep.mapIterator]
    apply Nat.div_eq_of_lt _ |>.symm
    have hi := length_le_of_nextAtIdxSlow?_eq_done (by rw [h])
    omega

theorem length_stepSize [Iterator α Id β] [Finite α Id] [LawfulDeterministicIterator α Id]
    [IteratorAccess α Id] [IteratorLoop α Id Id] [LawfulIteratorLoop α Id Id]
    {it : Iter (α := α) β} {n : Nat} :
    (it.stepSize n).length = (it.length + (n - 1)) / (n - 1 + 1) := by
  simp [stepSize_eq_intermediateStepSize, Intermediate.length_stepSize]

end Std.Iter
