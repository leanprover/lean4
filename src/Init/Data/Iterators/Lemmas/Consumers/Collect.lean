/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Basic
public import Init.Data.Iterators.Lemmas.Consumers.Monadic.Collect
public import Init.Data.Iterators.Consumers.Access
import all Init.Data.Iterators.Consumers.Access
import all Init.Data.Iterators.Consumers.Collect
import all Init.Data.Iterators.Consumers.Total
import all Init.Data.Iterators.Consumers.Monadic.Total

public section

namespace Std
open Std.Iterators

theorem Iter.toArray_eq_toArray_toIterM {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toArray = it.toIterM.toArray.run :=
  (rfl)

theorem Iter.toList_eq_toList_toIterM {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toList = it.toIterM.toList.run :=
  (rfl)

theorem Iter.toListRev_eq_toListRev_toIterM {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toListRev = it.toIterM.toListRev.run :=
  (rfl)

@[simp]
theorem Iter.toArray_ensureTermination {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.ensureTermination.toArray = it.toArray :=
  (rfl)

@[simp]
theorem Iter.toList_ensureTermination {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.ensureTermination.toList = it.toList :=
  (rfl)

@[simp]
theorem Iter.toListRev_ensureTermination_eq_toListRev {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} : it.ensureTermination.toListRev = it.toListRev :=
  (rfl)

@[simp]
theorem IterM.toList_toIter {α β} [Iterator α Id β] [Finite α Id]
    {it : IterM (α := α) Id β} :
    it.toIter.toList = it.toList.run :=
  (rfl)

@[simp]
theorem IterM.toListRev_toIter {α β} [Iterator α Id β] [Finite α Id]
    {it : IterM (α := α) Id β} :
    it.toIter.toListRev = it.toListRev.run :=
  (rfl)

@[simp]
theorem Iter.toList_toArray {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toArray.toList = it.toList := by
  simp [toArray_eq_toArray_toIterM, toList_eq_toList_toIterM, ← IterM.toList_toArray]

theorem Iter.toList_toArray_ensureTermination {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.ensureTermination.toArray.toList = it.toList := by
  simp

@[simp]
theorem Iter.toArray_toList {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toList.toArray = it.toArray := by
  simp [toArray_eq_toArray_toIterM, toList_eq_toList_toIterM, ← IterM.toArray_toList]

theorem Iter.toArray_toList_ensureTermination {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.ensureTermination.toList.toArray = it.toArray := by
  simp

@[simp]
theorem Iter.reverse_toListRev [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toListRev.reverse = it.toList := by
  simp [toListRev_eq_toListRev_toIterM, toList_eq_toList_toIterM, ← IterM.reverse_toListRev]

theorem Iter.reverse_toListRev_ensureTermination [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.ensureTermination.toListRev.reverse = it.toList := by
  simp

theorem Iter.toListRev_eq {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toListRev = it.toList.reverse := by
  simp [Iter.toListRev_eq_toListRev_toIterM, Iter.toList_eq_toList_toIterM, IterM.toListRev_eq]

theorem Iter.toListRev_ensureTermination {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.ensureTermination.toListRev = it.toList.reverse := by
  simp [toListRev_eq]

theorem Iter.toArray_eq_match_step {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toArray = match it.step.val with
      | .yield it' out => #[out] ++ it'.toArray
      | .skip it' => it'.toArray
      | .done => #[] := by
  simp only [Iter.toArray_eq_toArray_toIterM, Iter.step]
  rw [IterM.toArray_eq_match_step, Id.run_bind]
  generalize it.toIterM.step.run = step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp

theorem Iter.toArray_ensureTermination_eq_match_step {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.ensureTermination.toArray = match it.step.val with
      | .yield it' out => #[out] ++ it'.toArray
      | .skip it' => it'.toArray
      | .done => #[] := by
  rw [toArray_ensureTermination, toArray_eq_match_step]

theorem Iter.toList_eq_match_step {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toList = match it.step.val with
      | .yield it' out => out :: it'.toList
      | .skip it' => it'.toList
      | .done => [] := by
  rw [← Iter.toList_toArray, Iter.toArray_eq_match_step]
  split <;> simp [Iter.toList_toArray]

theorem Iter.toList_ensureTermination_eq_match_step {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.ensureTermination.toList = match it.step.val with
      | .yield it' out => out :: it'.toList
      | .skip it' => it'.toList
      | .done => [] := by
  rw [toList_ensureTermination, toList_eq_match_step]

theorem Iter.toListRev_eq_match_step {α β} [Iterator α Id β] [Finite α Id] {it : Iter (α := α) β} :
    it.toListRev = match it.step.val with
      | .yield it' out => it'.toListRev ++ [out]
      | .skip it' => it'.toListRev
      | .done => [] := by
  rw [Iter.toListRev_eq_toListRev_toIterM, IterM.toListRev_eq_match_step, Iter.step, Id.run_bind]
  generalize it.toIterM.step.run = step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp

theorem Iter.toListRev_ensureTermination_eq_match_step {α β} [Iterator α Id β] [Finite α Id] {it : Iter (α := α) β} :
    it.ensureTermination.toListRev = match it.step.val with
      | .yield it' out => it'.toListRev ++ [out]
      | .skip it' => it'.toListRev
      | .done => [] := by
  rw [toListRev_ensureTermination_eq_toListRev, toListRev_eq_match_step]

theorem Iter.getElem?_toList_eq_atIdxSlow? {α β}
    [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} {k : Nat} :
    it.toList[k]? = it.atIdxSlow? k := by
  induction it using Iter.inductSteps generalizing k with | step it ihy ihs
  rw [toList_eq_match_step, atIdxSlow?]
  obtain ⟨step, h⟩ := it.step
  cases step
  · cases k <;> simp [ihy h]
  · simp [ihs h]
  · simp

theorem Iter.toList_eq_of_atIdxSlow?_eq {α₁ α₂ β}
    [Iterator α₁ Id β] [Finite α₁ Id]
    [Iterator α₂ Id β] [Finite α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β}
    (h : ∀ k, it₁.atIdxSlow? k = it₂.atIdxSlow? k) :
    it₁.toList = it₂.toList := by
  ext; simp [getElem?_toList_eq_atIdxSlow?, h]

theorem Iter.isPlausibleIndirectOutput_of_mem_toList
    [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} {b : β} :
    b ∈ it.toList → it.IsPlausibleIndirectOutput b := by
  induction it using Iter.inductSteps with | step it ihy ihs
  rw [toList_eq_match_step]
  cases it.step using PlausibleIterStep.casesOn
  case yield it' out h =>
    simp only [List.mem_cons]
    rintro h'
    cases h' <;> rename_i h'
    · cases h'
      exact .direct ⟨_, h⟩
    · specialize ihy h h'
      exact IsPlausibleIndirectOutput.indirect ⟨_, rfl, h⟩ ihy
  case skip it' h =>
    simp only
    intro h'
    specialize ihs h h'
    exact IsPlausibleIndirectOutput.indirect ⟨_, rfl, h⟩ ihs
  case done h =>
    simp

theorem Iter.isPlausibleIndirectOutput_of_mem_toListRev
    [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} {b : β} :
    b ∈ it.toListRev → it.IsPlausibleIndirectOutput b := by
  intro h
  apply isPlausibleIndirectOutput_of_mem_toList
  simpa [toListRev_eq] using h

theorem Iter.isPlausibleIndirectOutput_of_mem_toArray
    [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} {b : β} :
    b ∈ it.toArray → it.IsPlausibleIndirectOutput b := by
  intro h
  apply isPlausibleIndirectOutput_of_mem_toList
  rw [← Array.mem_toList_iff] at h
  simpa [toList_toArray] using h

end Std
