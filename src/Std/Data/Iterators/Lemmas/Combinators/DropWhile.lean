/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Combinators.DropWhile
import Std.Data.Iterators.Lemmas.Combinators.Monadic.DropWhile
import Init.Data.Iterators.Lemmas.Consumers

namespace Std.Iterators

theorem Iter.dropWhile_eq_intermediateDropWhile {α β} [Iterator α Id β] {P}
    {it : Iter (α := α) β} :
    it.dropWhile P = Intermediate.dropWhile P true it :=
  rfl

theorem Iter.Intermediate.dropWhile_eq_dropWhile_toIterM {α β} [Iterator α Id β] {P}
    {it : Iter (α := α) β} {dropping} :
    Intermediate.dropWhile P dropping it =
      (IterM.Intermediate.dropWhile P dropping it.toIterM).toIter :=
  rfl

theorem Iter.dropWhile_eq_dropWhile_toIterM {α β} [Iterator α Id β] {P}
    {it : Iter (α := α) β} :
    it.dropWhile P = (it.toIterM.dropWhile P).toIter :=
  rfl

theorem Iter.step_intermediateDropWhile {α β} [Iterator α Id β]
    {it : Iter (α := α) β} {P} {dropping} :
    (Iter.Intermediate.dropWhile P dropping it).step = (match it.step with
      | .yield it' out h =>
        if h' : dropping = true then
          match P out with
          | true =>
            .skip (Intermediate.dropWhile P true it') (.dropped h h' True.intro)
          | false =>
            .yield (Intermediate.dropWhile P false it') out (.start h h' True.intro)
        else
          .yield (Intermediate.dropWhile P false it') out
              (.yield h (Bool.not_eq_true _ ▸ h'))
      | .skip it' h =>
        .skip (Intermediate.dropWhile P dropping it') (.skip h)
      | .done h =>
        .done (.done h)) := by
  simp [Intermediate.dropWhile_eq_dropWhile_toIterM, Iter.step, IterM.step_intermediateDropWhile]
  cases it.toIterM.step.run using PlausibleIterStep.casesOn
  · simp only [IterM.Step.toPure_yield, PlausibleIterStep.yield, toIter_toIterM, toIterM_toIter]
    split
    · split
      · split
        · rfl
        · exfalso; simp_all
      · split
        · exfalso; simp_all
        · rfl
    · rfl
  · rfl
  · rfl

theorem Iter.step_dropWhile {α β} [Iterator α Id β] {P}
    {it : Iter (α := α) β} :
    (it.dropWhile P).step = (match it.step with
    | .yield it' out h =>
        match P out with
        | true =>
          .skip (Intermediate.dropWhile P true it') (.dropped h rfl True.intro)
        | false =>
          .yield (Intermediate.dropWhile P false it') out (.start h rfl True.intro)
    | .skip it' h =>
      .skip (Intermediate.dropWhile P true it') (.skip h)
    | .done h =>
      .done (.done h)) := by
  simp [dropWhile_eq_intermediateDropWhile, step_intermediateDropWhile]

theorem Iter.toList_intermediateDropWhile_of_finite {α β} [Iterator α Id β] {P dropping}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (Intermediate.dropWhile P dropping it).toList =
      if dropping = true then it.toList.dropWhile P else it.toList := by
  induction it using Iter.inductSteps generalizing dropping with | step it ihy ihs =>
  rw [toList_eq_match_step, toList_eq_match_step, step_intermediateDropWhile]
  cases it.step using PlausibleIterStep.casesOn
  · rename_i hp
    simp [List.dropWhile_cons]
    cases P _
    · cases dropping
      · specialize ihy hp (dropping := false)
        rw [if_neg (by simp)] at ihy
        simp [ihy]
      · specialize ihy hp (dropping := false)
        rw [if_neg (by simp)] at ihy
        simp [ihy]
    · cases dropping
      · specialize ihy hp (dropping := false)
        simp [ihy]
      · specialize ihy hp (dropping := true)
        simp [ihy]
  · rename_i hp
    simp [ihs hp]
  · simp

@[simp]
theorem Iter.toList_dropWhile_of_finite {α β} [Iterator α Id β] {P}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (it.dropWhile P).toList = it.toList.dropWhile P := by
  simp [dropWhile_eq_intermediateDropWhile, toList_intermediateDropWhile_of_finite]

@[simp]
theorem Iter.toArray_dropWhile_of_finite {α β} [Iterator α Id β] {P}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (it.dropWhile P).toArray = (it.toList.dropWhile P).toArray := by
  simp only [← toArray_toList, toList_dropWhile_of_finite]

@[simp]
theorem Iter.toListRev_dropWhile_of_finite {α β} [Iterator α Id β] {P}
    [Finite α Id] [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id]
    {it : Iter (α := α) β} :
    (it.dropWhile P).toListRev = (it.toList.dropWhile P).reverse := by
  rw [toListRev_eq, toList_dropWhile_of_finite]

end Std.Iterators
