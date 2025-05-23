/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Array.Lemmas
import Std.Data.Iterators.Consumers.Monadic.Collect
import Std.Data.Iterators.Lemmas.Monadic.Basic
import Std.Data.Iterators.Producers

namespace Std.Iterators

section Consumers

theorem IterM.DefaultConsumers.toArrayMapped.go.aux₁ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {b : γ} {bs : Array γ} {f : β → m γ} :
    IterM.DefaultConsumers.toArrayMapped.go f it (#[b] ++ bs) = (#[b] ++ ·) <$> IterM.DefaultConsumers.toArrayMapped.go f it bs := by
  induction it, bs using IterM.DefaultConsumers.toArrayMapped.go.induct
  next it bs ih₁ ih₂ =>
  rw [go, map_eq_pure_bind, go, bind_assoc]
  apply bind_congr
  intro step
  split
  · simp [ih₁ _ _ ‹_›]
  · simp [ih₂ _ ‹_›]
  · simp

theorem IterM.DefaultConsumers.toArrayMapped.go.aux₂ [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {it : IterM (α := α) m β} {acc : Array γ} {f : β → m γ} :
    IterM.DefaultConsumers.toArrayMapped.go f it acc =
      (acc ++ ·) <$> IterM.DefaultConsumers.toArrayMapped f it := by
  rw [← Array.toArray_toList (xs := acc)]
  generalize acc.toList = acc
  induction acc with
  | nil => simp [toArrayMapped]
  | cons x xs ih =>
    rw [List.toArray_cons, IterM.DefaultConsumers.toArrayMapped.go.aux₁, ih]
    simp only [Functor.map_map, Array.append_assoc]

theorem IterM.DefaultConsumers.toArrayMapped_eq_match_step [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] {it : IterM (α := α) m β} {f : β → m γ} :
    IterM.DefaultConsumers.toArrayMapped f it = (do
      match ← it.step with
      | .yield it' out _ => return #[← f out] ++ (← IterM.DefaultConsumers.toArrayMapped f it')
      | .skip it' _ => IterM.DefaultConsumers.toArrayMapped f it'
      | .done _ => return #[]) := by
  rw [IterM.DefaultConsumers.toArrayMapped, IterM.DefaultConsumers.toArrayMapped.go]
  apply bind_congr
  intro step
  split <;> simp [IterM.DefaultConsumers.toArrayMapped.go.aux₂]

theorem IterM.toArray_eq_match_step [Monad m] [LawfulMonad m]
    [Iterator α m β] [Finite α m] [IteratorCollect α m] [LawfulIteratorCollect α m]
    {it : IterM (α := α) m β} :
    it.toArray = (do
      match ← it.step with
      | .yield it' out _ => return #[out] ++ (← it'.toArray)
      | .skip it' _ => it'.toArray
      | .done _ => return #[]) := by
  simp only [IterM.toArray, LawfulIteratorCollect.toArrayMapped_eq]
  rw [IterM.DefaultConsumers.toArrayMapped_eq_match_step]
  simp [bind_pure_comp, pure_bind, toArray]

theorem IterM.toList_toArray [Monad m] [Iterator α m β] [Finite α m] [IteratorCollect α m]
    {it : IterM (α := α) m β} :
    Array.toList <$> it.toArray = it.toList := by
  simp [IterM.toList]

theorem IterM.toArray_toList [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m] {it : IterM (α := α) m β} :
    List.toArray <$> it.toList = it.toArray := by
  simp [IterM.toList]

theorem IterM.toList_eq_match_step [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m] [LawfulIteratorCollect α m] {it : IterM (α := α) m β} :
    it.toList = (do
      match ← it.step with
      | .yield it' out _ => return out :: (← it'.toList)
      | .skip it' _ => it'.toList
      | .done _ => return []) := by
  simp [← IterM.toList_toArray]
  rw [IterM.toArray_eq_match_step, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  split <;> simp

theorem IterM.toListRev.go.aux₁ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    {it : IterM (α := α) m β} {b : β} {bs : List β} :
    IterM.toListRev.go it (bs ++ [b]) = (· ++ [b]) <$> IterM.toListRev.go it bs:= by
  induction it, bs using IterM.toListRev.go.induct
  next it bs ih₁ ih₂ =>
  rw [go, go, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  simp only [List.cons_append] at ih₁
  split <;> simp [*]

theorem IterM.toListRev.go.aux₂ [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
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
      match ← it.step with
      | .yield it' out _ => return (← it'.toListRev) ++ [out]
      | .skip it' _ => it'.toListRev
      | .done _ => return []) := by
  simp [IterM.toListRev]
  rw [toListRev.go]
  apply bind_congr
  intro step
  cases step using PlausibleIterStep.casesOn <;> simp [IterM.toListRev.go.aux₂]

theorem IterM.reverse_toListRev [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m] [LawfulIteratorCollect α m]
    {it : IterM (α := α) m β} :
    List.reverse <$> it.toListRev = it.toList := by
  apply Eq.symm
  induction it using IterM.inductSteps
  rename_i it ihy ihs
  rw [toListRev_eq_match_step, toList_eq_match_step, map_eq_pure_bind, bind_assoc]
  apply bind_congr
  intro step
  split <;> simp (discharger := assumption) [ihy, ihs]

theorem IterM.toListRev_eq [Monad m] [LawfulMonad m] [Iterator α m β] [Finite α m]
    [IteratorCollect α m] [LawfulIteratorCollect α m]
    {it : IterM (α := α) m β} :
    it.toListRev = List.reverse <$> it.toList := by
  rw [← IterM.reverse_toListRev]
  simp

end Consumers

end Std.Iterators
