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

namespace Std
open Std.Iterators Std.Internal

variable {α β : Type w} {m : Type w → Type w'} {it : IterM (α := α) m β}

private theorem IterM.toArray.go_eq [Monad m]
    [Iterator α m β] [LawfulMonad m] [Finite α m] {acc : Array β} :
    go it acc (m := m) = (do
      match (← it.step).inflate.val with
      | .yield it' out => go it' (acc.push out)
      | .skip it' => go it' acc
      | .done => return acc) := by
  rw [toArray.go, WellFounded.extrinsicFix₂_eq_apply]
  · simp only
    apply bind_congr; intro step
    cases step.inflate using PlausibleIterStep.casesOn <;> simp [go]
  · simp only [show (IterM.finitelyManySteps! = IterM.finitelyManySteps) by rfl]
    apply InvImage.wf
    exact WellFoundedRelation.wf

private theorem IterM.toArray.go.aux₁ [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {b : β} {bs : Array β} :
    IterM.toArray.go it (#[b] ++ bs) (m := m) =
      (#[b] ++ ·) <$> IterM.toArray.go it bs (m := m) := by
  induction it using IterM.inductSteps generalizing bs with | step it ihy ihs
  rw [go_eq, map_eq_pure_bind, go_eq, bind_assoc]
  apply bind_congr; intro step
  cases step.inflate using PlausibleIterStep.casesOn <;> simp (discharger := assumption) [ihy, ihs]

private theorem IterM.toArray.go.aux₂ [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {acc : Array β} :
    IterM.toArray.go it acc (m := m) =
      (acc ++ ·) <$> it.toArray := by
  rw [← Array.toArray_toList (xs := acc)]
  generalize acc.toList = acc
  induction acc with
  | nil => simp [toArray]
  | cons x xs ih =>
    rw [List.toArray_cons, IterM.toArray.go.aux₁, ih]
    simp only [Functor.map_map, Array.append_assoc]

theorem IterM.toArray_eq_match_step [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] :
    IterM.toArray it (m := m) = (do
      match (← it.step).inflate.val with
      | .yield it' out => return #[out] ++ (← it'.toArray)
      | .skip it' => it'.toArray
      | .done => return #[]) := by
  rw [IterM.toArray, IterM.toArray.go_eq]
  apply bind_congr
  intro step
  cases step.inflate using PlausibleIterStep.casesOn <;>
    simp [IterM.toArray.go.aux₂]

@[simp]
theorem IterM.toArray_ensureTermination [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    it.ensureTermination.toArray = it.toArray :=
  (rfl)

theorem IterM.toArray_ensureTermination_eq_match_step [Monad m] [LawfulMonad m] [Iterator α m β]
    [Finite α m] :
    it.ensureTermination.toArray = (do
      match (← it.step).inflate.val with
      | .yield it' out => return #[out] ++ (← it'.toArray)
      | .skip it' => it'.toArray
      | .done => return #[]) := by
  rw [toArray_ensureTermination, toArray_eq_match_step]

@[simp]
theorem IterM.toList_ensureTermination [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    it.ensureTermination.toList = it.toList :=
  (rfl)

@[simp]
theorem IterM.toList_toArray [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    Array.toList <$> it.toArray = it.toList := by
  simp [IterM.toList]

theorem IterM.toList_toArray_ensureTermination [Monad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    Array.toList <$> it.ensureTermination.toArray = it.toList := by
  simp

@[simp]
theorem IterM.toArray_toList [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    List.toArray <$> it.toList = it.toArray := by
  simp [IterM.toList, -toList_toArray]

theorem IterM.toArray_toList_ensureTermination [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    List.toArray <$> it.ensureTermination.toList = it.toArray := by
  rw [toList_ensureTermination, toArray_toList]

theorem IterM.toList_eq_match_step [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
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
    [Finite α m] {it : IterM (α := α) m β} :
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
    [Finite α m]
    {it : IterM (α := α) m β} :
    List.reverse <$> it.ensureTermination.toListRev = it.toList := by
  rw [toListRev_ensureTermination_eq_toListRev, reverse_toListRev]

theorem IterM.toListRev_eq [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    it.toListRev = List.reverse <$> it.toList := by
  simp [← IterM.reverse_toListRev]

theorem IterM.toListRev_ensureTermination [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} :
    it.ensureTermination.toListRev = List.reverse <$> it.toList := by
  simp [← IterM.reverse_toListRev]

end Std
