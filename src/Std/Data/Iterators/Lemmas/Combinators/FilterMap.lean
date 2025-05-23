/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Lemmas.Consumers
import Std.Data.Iterators.Lemmas.Combinators.Monadic.FilterMap
import Std.Data.Iterators.Combinators.FilterMap

namespace Std.Iterators

theorem Iter.filterMapWithProof_eq {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {m : Type w → Type w'} [Monad m] {f : β → PostconditionT m (Option γ)} :
    it.filterMapWithProof f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapWithProof f) :=
  rfl

theorem Iter.filterWithProof_eq {α β} [Iterator α Id β] {it : Iter (α := α) β}
    {m : Type w → Type w'} [Monad m] {f : β → PostconditionT m (ULift Bool)} :
    it.filterWithProof f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterWithProof f) :=
  rfl

theorem Iter.mapWithProof_eq {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {m : Type w → Type w'} [Monad m] {f : β → PostconditionT m γ} :
    it.mapWithProof f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.mapWithProof f) :=
  rfl

theorem Iter.filterMapM_eq {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {m : Type w → Type w'} [Monad m]
    {f : β → m (Option γ)} :
    it.filterMapM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterMapM f) :=
  rfl

theorem Iter.filterM_eq {α β} [Iterator α Id β] {it : Iter (α := α) β}
    {m : Type w → Type w'} [Monad m] {f : β → m (ULift Bool)} :
    it.filterM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.filterM f) :=
  rfl

theorem Iter.mapM_eq {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {m : Type w → Type w'} [Monad m] {f : β → m γ} :
    it.mapM f = (letI : MonadLift Id m := ⟨pure⟩; it.toIterM.mapM f) :=
  rfl

theorem Iter.filterMap_eq {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → Option γ} :
    it.filterMap f = (it.toIterM.filterMap f).toIter :=
  rfl

theorem Iter.map_eq {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → γ} :
    it.map f = (it.toIterM.map f).toIter :=
  rfl

theorem Iter.filter_eq {α β} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → Bool} :
    it.filter f = (it.toIterM.filter f).toIter :=
  rfl

theorem Iter.step_filterMap {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → Option γ} :
    (it.filterMap f).step = match it.step with
      | .yield it' out h =>
        match h' : f out with
        | none => .skip (it'.filterMap f) (.yieldNone (out := out) h h')
        | some out' => .yield (it'.filterMap f) out' (.yieldSome (out := out) h h')
      | .skip it' h => .skip (it'.filterMap f) (.skip h)
      | .done h => .done (.done h) := by
  simp only [filterMap_eq, step, toIterM_toIter, Id.run, IterM.step_filterMap, Id.pure_eq,
    Id.bind_eq]
  generalize it.toIterM.step = step
  obtain ⟨step, h⟩ := step
  apply Subtype.ext
  match step with
  | .yield it' out =>
    simp only [PlausibleIterStep.map, IterStep.map_yield, id_eq, toIterM_toIter,
      PlausibleIterStep.yield, PlausibleIterStep.skip]
    split <;> split
    all_goals
      simp only [IterStep.map_yield, id_eq, reduceCtorEq]
      simp_all
  | .skip it' =>
    simp [PlausibleIterStep.map, IterStep.map_yield, id_eq, toIterM_toIter,
      PlausibleIterStep.skip]
  | .done =>
    simp [PlausibleIterStep.map, PlausibleIterStep.done]

def Iter.step_map {α β γ} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → γ} :
    (it.map f).step = match it.step with
      | .yield it' out h =>
        .yield (it'.map f) (f out) (.yieldSome (out := out) h ⟨⟨f out, rfl⟩, rfl⟩)
      | .skip it' h =>
        .skip (it'.map f) (.skip h)
      | .done h =>
        .done (.done h) := by
  simp only [map_eq, step, toIterM_toIter, Id.run, IterM.step_map, Id.pure_eq, Id.bind_eq]
  generalize it.toIterM.step = step
  obtain ⟨step, h⟩ := step
  cases step
  · simp [PlausibleIterStep.map, PlausibleIterStep.yield]
  · simp [PlausibleIterStep.map, PlausibleIterStep.skip]
  · simp [PlausibleIterStep.map, PlausibleIterStep.done]

def Iter.step_filter {α β} [Iterator α Id β] {it : Iter (α := α) β}
    {f : β → Bool} :
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
  simp only [filter_eq, step, toIterM_toIter, Id.run, IterM.step_filter, Id.pure_eq, Id.bind_eq]
  generalize it.toIterM.step = step
  obtain ⟨step, h⟩ := step
  cases step
  · simp only [PlausibleIterStep.map, IterStep.map_yield, id_eq, toIterM_toIter]
    split <;> simp [PlausibleIterStep.yield, PlausibleIterStep.skip]
  · simp [PlausibleIterStep.map, PlausibleIterStep.skip]
  · simp [PlausibleIterStep.map, PlausibleIterStep.done]

theorem Iter.toList_filterMap {α β γ} [Iterator α Id β] [IteratorCollect α Id] [LawfulIteratorCollect α Id]
    {f : β → Option γ} {it : Iter (α := α) β} :
    (it.filterMap f).toList = it.toList.filterMap f := by
  simp [filterMap_eq, toList_eq_toList_toIterM, IterM.toList_filterMap]

theorem Iter.toList_map {α β γ} [Iterator α Id β] [IteratorCollect α Id] [LawfulIteratorCollect α Id]
    {f : β → γ} {it : Iter (α := α) β} :
    (it.map f).toList = it.toList.map f := by
  simp [map_eq, IterM.toList_map, Iter.toList_eq_toList_toIterM]

theorem Iter.toList_filter {α β} [Iterator α Id β] [IteratorCollect α Id] [LawfulIteratorCollect α Id]
    {f : β → Bool} {it : Iter (α := α) β} :
    (it.filter f).toList = it.toList.filter f := by
  simp [filter_eq, IterM.toList_filter, Iter.toList_eq_toList_toIterM]

end Std.Iterators
