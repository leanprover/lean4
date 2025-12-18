/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Array.Lemmas
public import Init.Data.Iterators.Lemmas.Monadic.Basic
public import Init.Data.Iterators.Consumers.Monadic.Collect
import all Init.Data.Iterators.Consumers.Monadic.Collect
import all Init.Data.Iterators.Consumers.Monadic.Total
import all Init.WFExtrinsicFix

public section

namespace Std.Iterators
open Std.Internal

variable {α β γ : Type w} {m : Type w → Type w'} {n : Type w → Type w''}
  {lift : ⦃δ : Type w⦄ → m δ → n δ} {f : β → n γ} {it : IterM (α := α) m β}

private theorem IterM.DefaultConsumers.toArrayMapped.go_eq [Monad n]
    [Iterator α m β] [LawfulMonad n] [Finite α m] {acc : Array γ} :
    letI : MonadLift m n := ⟨lift (δ := _)⟩
    go lift f it acc (m := m) = (do
      match (← it.step).inflate.val with
      | .yield it' out => go lift f it' (acc.push (← f out))
      | .skip it' => go lift f it' acc
      | .done => return acc) := by
  letI : MonadLift m n := ⟨lift (δ := _)⟩
  rw [toArrayMapped.go, WellFounded.extrinsicFix₂_eq_apply]
  · simp only
    apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn
    · apply bind_congr; intro fx
      simp [go]
    · simp [go]
    · simp
  · simp only [show (IterM.finitelyManySteps! = IterM.finitelyManySteps) by rfl]
    apply InvImage.wf
    exact WellFoundedRelation.wf

private theorem IterM.DefaultConsumers.toArrayMapped.go.aux₁ [Monad n] [LawfulMonad n]
    [Iterator α m β] [Finite α m] {b : γ} {bs : Array γ} :
    IterM.DefaultConsumers.toArrayMapped.go lift f it (#[b] ++ bs) (m := m) =
      (#[b] ++ ·) <$> IterM.DefaultConsumers.toArrayMapped.go lift f it bs (m := m) := by
  induction it using IterM.inductSteps generalizing bs with | step it ihy ihs
  rw [go_eq, map_eq_pure_bind, go_eq, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp (discharger := assumption) [ihy, ihs]

private theorem IterM.DefaultConsumers.toArrayMapped.go.aux₂ [Monad n] [LawfulMonad n]
    [Iterator α m β] [Finite α m] {acc : Array γ} :
    IterM.DefaultConsumers.toArrayMapped.go lift f it acc (m := m) =
      (acc ++ ·) <$> IterM.DefaultConsumers.toArrayMapped lift f it (m := m) := by
  rw [← Array.toArray_toList (xs := acc)]
  generalize acc.toList = acc
  induction acc with
  | nil => simp [toArrayMapped]
  | cons x xs ih =>
    rw [List.toArray_cons, IterM.DefaultConsumers.toArrayMapped.go.aux₁, ih]
    simp only [Functor.map_map, Array.append_assoc]

theorem IterM.DefaultConsumers.toArrayMapped_eq_match_step [Monad n] [LawfulMonad n]
    [Iterator α m β] [Finite α m] :
    IterM.DefaultConsumers.toArrayMapped lift f it (m := m) = letI : MonadLift m n := ⟨lift (δ := _)⟩; (do
      match (← it.step).inflate.val with
      | .yield it' out =>
        return #[← f out] ++ (← IterM.DefaultConsumers.toArrayMapped lift f it' (m := m))
      | .skip it' => IterM.DefaultConsumers.toArrayMapped lift f it' (m := m)
      | .done => return #[]) := by
  rw [IterM.DefaultConsumers.toArrayMapped, IterM.DefaultConsumers.toArrayMapped.go_eq]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;>
    simp [IterM.DefaultConsumers.toArrayMapped.go.aux₂]

@[simp]
theorem IterM.toArray_ensureTermination [Monad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] {it : IterM (α := α) m β} :
    it.ensureTermination.toArray = it.toArray :=
  (rfl)

theorem IterM.toArray_eq_match_step [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] [LawfulIteratorCollect α m m] :
    it.toArray = (do
      match (← it.step).inflate.val with
      | .yield it' out => return #[out] ++ (← it'.toArray)
      | .skip it' => it'.toArray
      | .done => return #[]) := by
  simp only [IterM.toArray, LawfulIteratorCollect.toArrayMapped_eq]
  rw [IterM.DefaultConsumers.toArrayMapped_eq_match_step]
  simp [bind_pure_comp, pure_bind]

theorem IterM.toArray_ensureTermination_eq_match_step [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m] :
    it.ensureTermination.toArray = (do
      match (← it.step).inflate.val with
      | .yield it' out => return #[out] ++ (← it'.toArray)
      | .skip it' => it'.toArray
      | .done => return #[]) := by
  rw [toArray_ensureTermination, toArray_eq_match_step]

@[simp]
theorem IterM.toList_ensureTermination [Monad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] {it : IterM (α := α) m β} :
    it.ensureTermination.toList = it.toList :=
  (rfl)

@[simp]
theorem IterM.toList_toArray [Monad m] [Iterator α m β] [Finite α m] [IteratorCollect α m m]
    {it : IterM (α := α) m β} :
    Array.toList <$> it.toArray = it.toList := by
  simp [IterM.toList]

theorem IterM.toList_toArray_ensureTermination [Monad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] {it : IterM (α := α) m β} :
    Array.toList <$> it.ensureTermination.toArray = it.toList := by
  simp

@[simp]
theorem IterM.toArray_toList [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] {it : IterM (α := α) m β} :
    List.toArray <$> it.toList = it.toArray := by
  simp [IterM.toList, -toList_toArray]

theorem IterM.toArray_toList_ensureTermination [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] {it : IterM (α := α) m β} :
    List.toArray <$> it.ensureTermination.toList = it.toArray := by
  rw [toList_ensureTermination, toArray_toList]

theorem IterM.toList_eq_match_step [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] [LawfulIteratorCollect α m m] {it : IterM (α := α) m β} :
    it.toList = (do
      match (← it.step).inflate.val with
      | .yield it' out => return out :: (← it'.toList)
      | .skip it' => it'.toList
      | .done => return []) := by
  simp [← IterM.toList_toArray]
  rw [IterM.toArray_eq_match_step, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  split <;> simp

theorem IterM.toList_ensureTermination_eq_match_step [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m] {it : IterM (α := α) m β} :
    it.ensureTermination.toList = (do
      match (← it.step).inflate.val with
      | .yield it' out => return out :: (← it'.toList)
      | .skip it' => it'.toList
      | .done => return []) := by
  rw [toList_ensureTermination, toList_eq_match_step]

@[simp]
theorem IterM.toListRev_ensureTermination_eq_toListRev [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    it.ensureTermination.toListRev = it.toListRev :=
  (rfl)

private theorem IterM.toListRev.go_eq [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {bs : List β} :
    go it bs = (do
      match (← it.step).inflate.val with
      | .yield it' out => go it' (out :: bs)
      | .skip it' => go it' bs
      | .done => return bs) := by
  rw [go, WellFounded.extrinsicFix₂_eq_apply]
  · apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> simp [go]
  · simp only [show (IterM.finitelyManySteps! = IterM.finitelyManySteps) by rfl]
    apply InvImage.wf
    exact WellFoundedRelation.wf

private theorem IterM.toListRev.go.aux₁ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {b : β} {bs : List β} :
    IterM.toListRev.go it (bs ++ [b]) = (· ++ [b]) <$> IterM.toListRev.go it bs:= by
  induction it using IterM.inductSteps generalizing bs with | step it ihy ihs
  rw [go_eq, go_eq, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn
  · simpa using ihy ‹_› (bs := _ :: bs)
  · simpa using ihs ‹_›
  · simp


private theorem IterM.toListRev.go.aux₂ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {acc : List β} :
    IterM.toListRev.go it acc = (· ++ acc) <$> it.toListRev := by
  rw [← List.reverse_reverse (as := acc)]
  generalize acc.reverse = acc
  induction acc with
  | nil => simp [toListRev]
  | cons x xs ih => simp [IterM.toListRev.go.aux₁, ih]

theorem IterM.toListRev_eq_match_step [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    it.toListRev = (do
      match (← it.step).inflate.val with
      | .yield it' out => return (← it'.toListRev) ++ [out]
      | .skip it' => it'.toListRev
      | .done => return []) := by
  simp [IterM.toListRev]
  rw [toListRev.go_eq]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp [IterM.toListRev.go.aux₂]

theorem IterM.toListRev_ensureTermination_eq_match_step [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite α m] {it : IterM (α := α) m β} :
    it.ensureTermination.toListRev = (do
      match (← it.step).inflate.val with
      | .yield it' out => return (← it'.toListRev) ++ [out]
      | .skip it' => it'.toListRev
      | .done => return []) := by
  rw [toListRev_ensureTermination_eq_toListRev, toListRev_eq_match_step]

@[simp]
theorem IterM.reverse_toListRev [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    List.reverse <$> it.toListRev = it.toList := by
  apply Eq.symm
  induction it using IterM.inductSteps
  rename_i it ihy ihs
  rw [toListRev_eq_match_step, toList_eq_match_step, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp (discharger := assumption) [ihy, ihs]

@[simp]
theorem IterM.reverse_toListRev_ensureTermination [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite α m] [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    List.reverse <$> it.ensureTermination.toListRev = it.toList := by
  rw [toListRev_ensureTermination_eq_toListRev, reverse_toListRev]

theorem IterM.toListRev_eq [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    it.toListRev = List.reverse <$> it.toList := by
  simp [← IterM.reverse_toListRev]

theorem IterM.toListRev_ensureTermination [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m m] [LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    it.ensureTermination.toListRev = List.reverse <$> it.toList := by
  simp [← IterM.reverse_toListRev]

theorem LawfulIteratorCollect.toArray_eq {α β : Type w} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] [Finite α m] [IteratorCollect α m m]
    [hl : LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    it.toArray = (letI : IteratorCollect α m m := .defaultImplementation; it.toArray) := by
  simp [IterM.toArray, toArrayMapped_eq, IteratorCollect.defaultImplementation]

theorem LawfulIteratorCollect.toList_eq {α β : Type w} {m : Type w → Type w'}
    [Monad m] [Iterator α m β] [Finite α m] [IteratorCollect α m m]
    [hl : LawfulIteratorCollect α m m]
    {it : IterM (α := α) m β} :
    it.toList = (letI : IteratorCollect α m m := .defaultImplementation; it.toList) := by
  simp [IterM.toList, toArray_eq, -IterM.toList_toArray]

end Std.Iterators
