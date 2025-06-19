/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Iterators.Lemmas.Consumers
import Std.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
import Std.Data.Iterators.Combinators.FilterMap

namespace Std.Iterators

variable {α β γ : Type w} [Iterator α Id β] {it : Iter (α := α) β}
    {m : Type w → Type w'} {n : Type w → Type w''}

theorem Iter.filterMapWithPostcondition_eq_toIter_filterMapWithPostcondition_toIterM [Monad m]
    {f : β → PostconditionT m (Option γ)} :
    it.filterMapWithPostcondition f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapWithPostcondition f) :=
  rfl

theorem Iter.filterWithPostcondition_eq_toIter_filterMapWithPostcondition_toIterM [Monad m]
    {f : β → PostconditionT m (ULift Bool)} :
    it.filterWithPostcondition f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterWithPostcondition f) :=
  rfl

theorem Iter.mapWithPostcondition_eq_toIter_mapWithPostcondition_toIterM [Monad m] {f : β → PostconditionT m γ} :
    it.mapWithPostcondition f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.mapWithPostcondition f) :=
  rfl

theorem Iter.filterMapM_eq_toIter_filterMapM_toIterM [Monad m] {f : β → m (Option γ)} :
    it.filterMapM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapM f) :=
  rfl

theorem Iter.filterM_eq_toIter_filterM_toIterM [Monad m] {f : β → m (ULift Bool)} :
    it.filterM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterM f) :=
  rfl

theorem Iter.mapM_eq_toIter_mapM_toIterM [Monad m] {f : β → m γ} :
    it.mapM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.mapM f) :=
  rfl

theorem Iter.filterMap_eq_toIter_filterMap_toIterM {f : β → Option γ} :
    it.filterMap f = (it.toIterM.filterMap f).toIter :=
  rfl

theorem Iter.map_eq_toIter_map_toIterM {f : β → γ} :
    it.map f = (it.toIterM.map f).toIter :=
  rfl

theorem Iter.filter_eq_toIter_filter_toIterM [Monad m] {f : β → Bool} :
    it.filter f = (it.toIterM.filter f).toIter :=
  rfl

theorem Iter.step_filterMapWithPostcondition {f : β → PostconditionT n (Option γ)}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapWithPostcondition f).step = (do
    match it.step with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨none, h'⟩ =>
        pure <| .skip (it'.filterMapWithPostcondition f) (.yieldNone (out := out) h h')
      | ⟨some out', h'⟩ =>
        pure <| .yield (it'.filterMapWithPostcondition f) out' (.yieldSome (out := out) h h')
    | .skip it' h =>
      pure <| .skip (it'.filterMapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  simp only [filterMapWithPostcondition_eq_toIter_filterMapWithPostcondition_toIterM, IterM.step_filterMapWithPostcondition,
    step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step with
  | .yield it' out h =>
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_filterWithPostcondition {f : β → PostconditionT n (ULift Bool)}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterWithPostcondition f).step = (do
    match it.step with
    | .yield it' out h => do
      match ← (f out).operation with
      | ⟨.up false, h'⟩ =>
        pure <| .skip (it'.filterWithPostcondition f) (.yieldNone (out := out) h ⟨⟨_, h'⟩, rfl⟩)
      | ⟨.up true, h'⟩ =>
        pure <| .yield (it'.filterWithPostcondition f) out (.yieldSome (out := out) h ⟨⟨_, h'⟩, rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.filterWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  simp only [filterWithPostcondition_eq_toIter_filterMapWithPostcondition_toIterM, IterM.step_filterWithPostcondition, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step with
  | .yield it' out h =>
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_mapWithPostcondition {f : β → PostconditionT n γ}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.mapWithPostcondition f).step = (do
    match it.step with
    | .yield it' out h => do
      let out' ← (f out).operation
      pure <| .yield (it'.mapWithPostcondition f) out'.1 (.yieldSome h ⟨out', rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.mapWithPostcondition f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  simp only [mapWithPostcondition_eq_toIter_mapWithPostcondition_toIterM, IterM.step_mapWithPostcondition, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step with
  | .yield it' out h =>
    simp only [PostconditionT.operation_map, bind_map_left, bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_filterMapM {β' : Type w} {f : β → n (Option β')}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterMapM f).step = (do
    match it.step with
    | .yield it' out h => do
      match ← f out with
      | none =>
        pure <| .skip (it'.filterMapM f) (.yieldNone (out := out) h .intro)
      | some out' =>
        pure <| .yield (it'.filterMapM f) out' (.yieldSome (out := out) h .intro)
    | .skip it' h =>
      pure <| .skip (it'.filterMapM f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  simp only [filterMapM_eq_toIter_filterMapM_toIterM, IterM.step_filterMapM, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step with
  | .yield it' out h =>
    simp only [monadLift, MonadLift.monadLift, monadLift_self, bind_map_left]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_filterM {f : β → n (ULift Bool)}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.filterM f).step = (do
    match it.step with
    | .yield it' out h => do
      match ← f out with
      | .up false =>
        pure <| .skip (it'.filterM f) (.yieldNone (out := out) h ⟨⟨.up false, .intro⟩, rfl⟩)
      | .up true =>
        pure <| .yield (it'.filterM f) out (.yieldSome (out := out) h ⟨⟨.up true, .intro⟩, rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.filterM f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  simp only [filterM_eq_toIter_filterM_toIterM, IterM.step_filterM, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step with
  | .yield it' out h =>
    simp [PostconditionT.lift, liftM, monadLift, MonadLift.monadLift]
    apply bind_congr
    intro step
    rcases step with _ | _ <;> rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_mapM {f : β → n γ}
    [Monad n] [LawfulMonad n] [MonadLiftT m n] :
  (it.mapM f).step = (do
    match it.step with
    | .yield it' out h => do
      let out' ← f out
      pure <| .yield (it'.mapM f) out' (.yieldSome h ⟨⟨out', True.intro⟩, rfl⟩)
    | .skip it' h =>
      pure <| .skip (it'.mapM f) (.skip h)
    | .done h =>
      pure <| .done (.done h)) := by
  simp only [mapM_eq_toIter_mapM_toIterM, IterM.step_mapM, step]
  simp only [liftM, monadLift, pure_bind]
  generalize it.toIterM.step = step
  match step with
  | .yield it' out h =>
    simp only [PostconditionT.operation_map, bind_map_left, bind_pure_comp]
    simp only [monadLift, MonadLift.monadLift, monadLift_self, Functor.map, Functor.map_map,
      bind_map_left, bind_pure_comp]
    rfl
  | .skip it' h => rfl
  | .done h => rfl

theorem Iter.step_filterMap {f : β → Option γ} :
    (it.filterMap f).step = match it.step with
      | .yield it' out h =>
        match h' : f out with
        | none => .skip (it'.filterMap f) (.yieldNone (out := out) h h')
        | some out' => .yield (it'.filterMap f) out' (.yieldSome (out := out) h h')
      | .skip it' h => .skip (it'.filterMap f) (.skip h)
      | .done h => .done (.done h) := by
  simp only [filterMap_eq_toIter_filterMap_toIterM, toIterM_toIter, IterM.step_filterMap, step]
  simp only [liftM, monadLift, pure_bind, Id.run_bind]
  generalize it.toIterM.step.run = step
  cases step using PlausibleIterStep.casesOn
  · simp only [IterM.Step.toPure_yield, toIter_toIterM, toIterM_toIter]
    split <;> split <;> (try exfalso; simp_all; done)
    · rfl
    · rename_i h₁ _ h₂
      rw [h₁] at h₂
      cases h₂
      rfl
  · simp
  · simp

theorem Iter.step_map {f : β → γ} :
    (it.map f).step = match it.step with
      | .yield it' out h =>
        .yield (it'.map f) (f out) (.yieldSome (out := out) h ⟨⟨f out, rfl⟩, rfl⟩)
      | .skip it' h =>
        .skip (it'.map f) (.skip h)
      | .done h =>
        .done (.done h) := by
  simp only [map_eq_toIter_map_toIterM, step, toIterM_toIter, IterM.step_map, Id.run_bind]
  generalize it.toIterM.step.run = step
  cases step using PlausibleIterStep.casesOn <;> simp

def Iter.step_filter {f : β → Bool} :
    (it.filter f).step = match it.step with
      | .yield it' out h =>
        if h' : f out = true then
          .yield (it'.filter f) out (.yieldSome (out := out) h (by simp [h']))
        else
          .skip (it'.filter f) (.yieldNone h (by simp [h']))
      | .skip it' h =>
        .skip (it'.filter f) (.skip h)
      | .done h =>
        .done (.done h) := by
  simp only [filter_eq_toIter_filter_toIterM, step, toIterM_toIter, IterM.step_filter, Id.run_bind]
  generalize it.toIterM.step.run = step
  cases step using PlausibleIterStep.casesOn
  · simp only
    split <;> simp [*]
  · simp
  · simp

@[simp]
theorem Iter.toList_filterMap
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Option γ} :
    (it.filterMap f).toList = it.toList.filterMap f := by
  simp [filterMap_eq_toIter_filterMap_toIterM, toList_eq_toList_toIterM, IterM.toList_filterMap]

@[simp]
theorem Iter.toList_map
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → γ} :
    (it.map f).toList = it.toList.map f := by
  simp [map_eq_toIter_map_toIterM, IterM.toList_map, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toList_filter
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Bool} :
    (it.filter f).toList = it.toList.filter f := by
  simp [filter_eq_toIter_filter_toIterM, IterM.toList_filter, Iter.toList_eq_toList_toIterM]

@[simp]
theorem Iter.toListRev_filterMap
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Option γ} :
    (it.filterMap f).toListRev = it.toListRev.filterMap f := by
  simp [filterMap_eq_toIter_filterMap_toIterM, toListRev_eq_toListRev_toIterM, IterM.toListRev_filterMap]

@[simp]
theorem Iter.toListRev_map
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → γ} :
    (it.map f).toListRev = it.toListRev.map f := by
  simp [map_eq_toIter_map_toIterM, IterM.toListRev_map, Iter.toListRev_eq_toListRev_toIterM]

@[simp]
theorem Iter.toListRev_filter
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Bool} :
    (it.filter f).toListRev = it.toListRev.filter f := by
  simp [filter_eq_toIter_filter_toIterM, IterM.toListRev_filter, Iter.toListRev_eq_toListRev_toIterM]

@[simp]
theorem Iter.toArray_filterMap
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Option γ} :
    (it.filterMap f).toArray = it.toArray.filterMap f := by
  simp [filterMap_eq_toIter_filterMap_toIterM, toArray_eq_toArray_toIterM, IterM.toArray_filterMap]

@[simp]
theorem Iter.toArray_map
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → γ} :
    (it.map f).toArray = it.toArray.map f := by
  simp [map_eq_toIter_map_toIterM, IterM.toArray_map, Iter.toArray_eq_toArray_toIterM]

@[simp]
theorem Iter.toArray_filter
    [IteratorCollect α Id Id] [LawfulIteratorCollect α Id Id] [Finite α Id]
    {f : β → Bool} :
    (it.filter f).toArray = it.toArray.filter f := by
  simp [filter_eq_toIter_filter_toIterM, IterM.toArray_filter, Iter.toArray_eq_toArray_toIterM]

end Std.Iterators
