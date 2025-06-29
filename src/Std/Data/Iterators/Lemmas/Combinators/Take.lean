/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.Take
import Init.Data.Iterators.Consumers.Access
import Std.Data.Iterators.Lemmas.Combinators.Monadic.Take
import Init.Data.Iterators.Lemmas.Consumers

namespace Std.Iterators

theorem Iter.take_eq_toIter_take_toIterM {α β} [Iterator α Id β] {n : Nat}
    {it : Iter (α := α) β} :
    it.take n = (it.toIterM.take n).toIter :=
  rfl

theorem Iter.step_take {α β} [Iterator α Id β] {n : Nat}
    {it : Iter (α := α) β} :
    (it.take n).step = (match n with
      | 0 => .done (.depleted rfl)
      | k + 1 =>
        match it.step with
        | .yield it' out h => .yield (it'.take k) out (.yield h rfl)
        | .skip it' h => .skip (it'.take (k + 1)) (.skip h rfl)
        | .done h => .done (.done h)) := by
  simp only [Iter.step, Iter.step, Iter.take_eq_toIter_take_toIterM, IterM.step_take, toIterM_toIter]
  cases n
  case zero => simp [PlausibleIterStep.done]
  case succ k =>
    simp only [Id.run_bind]
    generalize it.toIterM.step.run = step
    cases step using PlausibleIterStep.casesOn <;>
      simp [PlausibleIterStep.yield, PlausibleIterStep.skip, PlausibleIterStep.done]

theorem Iter.atIdxSlow?_take {α β}
    [Iterator α Id β] [Productive α Id] {k l : Nat}
    {it : Iter (α := α) β} :
    (it.take k).atIdxSlow? l = if l < k then it.atIdxSlow? l else none := by
  fun_induction it.atIdxSlow? l generalizing k
  case case1 it it' out h h' =>
    simp only [atIdxSlow?.eq_def (it := it.take k), step_take, h']
    cases k <;> simp
  case case2 it it' out h h' l ih =>
    simp only [Nat.succ_eq_add_one, atIdxSlow?.eq_def (it := it.take k), step_take, h']
    cases k <;> cases l <;> simp [ih]
  case case3 l it it' h h' ih =>
    simp only [atIdxSlow?.eq_def (it := it.take k), step_take, h']
    cases k <;> cases l <;> simp [ih]
  case case4 l it h h' =>
    simp only [atIdxSlow?.eq_def (it := it.take k), step_take, h']
    cases k <;> cases l <;> simp

@[simp]
theorem Iter.toList_take_of_finite {α β} [Iterator α Id β] {n : Nat}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (it.take n).toList = it.toList.take n := by
  induction it using Iter.inductSteps generalizing n with | step it ihy ihs =>
  rw [Iter.toList_eq_match_step, Iter.toList_eq_match_step, Iter.step_take]
  cases n
  case zero => simp
  case succ k =>
    simp
    obtain ⟨step, h⟩ := it.step
    cases step
    · simp [ihy h]
    · simp [ihs h]
    · simp

@[simp]
theorem Iter.toListRev_take_of_finite {α β} [Iterator α Id β] {n : Nat}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (it.take n).toListRev = it.toListRev.drop (it.toList.length - n) := by
  rw [toListRev_eq, toList_take_of_finite, List.reverse_take, toListRev_eq]

@[simp]
theorem Iter.toArray_take_of_finite {α β} [Iterator α Id β] {n : Nat}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (it.take n).toArray = it.toArray.take n := by
  rw [← toArray_toList, ← toArray_toList, List.take_toArray, toList_take_of_finite]

@[simp]
theorem Iter.toList_take_zero {α β} [Iterator α Id β]
    [Finite (Take α Id β) Id]
    [IteratorCollect (Take α Id β) Id Id] [LawfulIteratorCollect (Take α Id β) Id Id]
    {it : Iter (α := α) β} :
    (it.take 0).toList = [] := by
  rw [toList_eq_match_step]
  simp [step_take]

end Std.Iterators
