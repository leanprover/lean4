/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Consumers.Access
import Std.Data.Iterators.Consumers.Collect
import Std.Data.Iterators.Lemmas.Basic
import Std.Data.Iterators.Lemmas.Consumers.Monadic.Collect

namespace Std.Iterators

theorem Iter.toArray_eq_toArray_toIterM {α β} [Iterator α Id β] [Finite α Id] [IteratorCollect α Id]
    [LawfulIteratorCollect α Id] {it : Iter (α := α) β} :
    it.toArray = it.toIterM.toArray :=
  rfl

theorem Iter.toList_eq_toList_toIterM {α β} [Iterator α Id β] [Finite α Id] [IteratorCollect α Id]
    [LawfulIteratorCollect α Id] {it : Iter (α := α) β} :
    it.toList = it.toIterM.toList :=
  rfl

theorem Iter.toListRev_eq_toListRev_toIterM {α β} [Iterator α Id β] [Finite α Id]
    {it : Iter (α := α) β} :
    it.toListRev = it.toIterM.toListRev :=
  rfl

@[simp]
theorem IterM.toList_toIter {α β} [Iterator α Id β] [Finite α Id] [IteratorCollect α Id]
    {it : IterM (α := α) Id β} :
    it.toIter.toList = it.toList :=
  rfl

@[simp]
theorem IterM.toListRev_toIter {α β} [Iterator α Id β] [Finite α Id]
    {it : IterM (α := α) Id β} :
    it.toIter.toListRev = it.toListRev :=
  rfl

theorem Iter.toList_toArray {α β} [Iterator α Id β] [Finite α Id] [IteratorCollect α Id]
    [LawfulIteratorCollect α Id] {it : Iter (α := α) β} :
    it.toArray.toList = it.toList := by
  simp only [toArray_eq_toArray_toIterM, toList_eq_toList_toIterM, ← IterM.toList_toArray,
    Id.map_eq]

theorem Iter.toArray_toList {α β} [Iterator α Id β] [Finite α Id] [IteratorCollect α Id]
    [LawfulIteratorCollect α Id] {it : Iter (α := α) β} :
    it.toList.toArray = it.toArray := by
  simp only [toArray_eq_toArray_toIterM, toList_eq_toList_toIterM, ← IterM.toArray_toList,
    Id.map_eq]

theorem Iter.toListRev_eq {α β} [Iterator α Id β] [Finite α Id] [IteratorCollect α Id]
    [LawfulIteratorCollect α Id] {it : Iter (α := α) β} :
    it.toListRev = it.toList.reverse := by
  simp [Iter.toListRev_eq_toListRev_toIterM, Iter.toList_eq_toList_toIterM, IterM.toListRev_eq]

theorem Iter.toArray_eq_match_step {α β} [Iterator α Id β] [Finite α Id] [IteratorCollect α Id]
    [LawfulIteratorCollect α Id] {it : Iter (α := α) β} :
    it.toArray = match it.step with
      | .yield it' out _ => #[out] ++ it'.toArray
      | .skip it' _ => it'.toArray
      | .done _ => #[] := by
  simp only [Iter.toArray_eq_toArray_toIterM, Iter.step]
  rw [IterM.toArray_eq_match_step]
  simp only [Id.map_eq, Id.pure_eq, Id.bind_eq, Id.run]
  generalize it.toIterM.step = step
  cases step using PlausibleIterStep.casesOn <;> simp

theorem Iter.toList_eq_match_step {α β} [Iterator α Id β] [Finite α Id] [IteratorCollect α Id]
    [LawfulIteratorCollect α Id] {it : Iter (α := α) β} :
    it.toList = match it.step with
      | .yield it' out _ => out :: it'.toList
      | .skip it' _ => it'.toList
      | .done _ => [] := by
  rw [← Iter.toList_toArray, Iter.toArray_eq_match_step]
  split <;> simp [Iter.toList_toArray]

theorem Iter.toListRev_eq_match_step {α β} [Iterator α Id β] [Finite α Id] {it : Iter (α := α) β} :
    it.toListRev = match it.step with
      | .yield it' out _ => it'.toListRev ++ [out]
      | .skip it' _ => it'.toListRev
      | .done _ => [] := by
  rw [Iter.toListRev_eq_toListRev_toIterM, IterM.toListRev_eq_match_step, Iter.step]
  simp only [Id.map_eq, Id.pure_eq, Id.bind_eq, Id.run]
  generalize it.toIterM.step = step
  cases step using PlausibleIterStep.casesOn <;> simp

theorem Iter.getElem?_toList_eq_seekIdx? {α β}
    [Iterator α Id β] [Finite α Id] [IteratorCollect α Id] [LawfulIteratorCollect α Id]
    {it : Iter (α := α) β} {k : Nat} :
    it.toList[k]? = it.seekIdx? k := by
  induction it using Iter.inductSteps generalizing k with | step it ihy ihs =>
  rw [toList_eq_match_step, seekIdx?]
  obtain ⟨step, h⟩ := it.step
  cases step
  · cases k <;> simp [ihy h]
  · simp [ihs h]
  · simp

theorem Iter.toList_eq_of_seekIdx?_eq {α₁ α₂ β}
    [Iterator α₁ Id β] [Finite α₁ Id] [IteratorCollect α₁ Id] [LawfulIteratorCollect α₁ Id]
    [Iterator α₂ Id β] [Finite α₂ Id] [IteratorCollect α₂ Id] [LawfulIteratorCollect α₂ Id]
    {it₁ : Iter (α := α₁) β} {it₂ : Iter (α := α₂) β}
    (h : ∀ k, it₁.seekIdx? k = it₂.seekIdx? k) :
    it₁.toList = it₂.toList := by
  ext; simp [getElem?_toList_eq_seekIdx?, h]

end Std.Iterators
