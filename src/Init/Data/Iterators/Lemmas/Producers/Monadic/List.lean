/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Consumers.Monadic
public import Init.Data.Iterators.Producers.Monadic.List

@[expose] public section

/-!
# Lemmas about list iterators

This module provides lemmas about the interactions of `List.iterM` with `IterM.step` and various
collectors.
-/

namespace Std.Iterators
open Std.Internal

variable {m : Type w → Type w'} {n : Type w → Type w''} [Monad m] {β : Type w}

@[simp]
theorem _root_.List.step_iterM_nil :
    (([] : List β).iterM m).step = pure (.deflate ⟨.done, rfl⟩) := by
  simp only [IterM.step, Iterator.step]; rfl

@[simp]
theorem _root_.List.step_iterM_cons {x : β} {xs : List β} :
    ((x :: xs).iterM m).step = pure (.deflate ⟨.yield (xs.iterM m) x, rfl⟩) := by
  simp only [List.iterM, IterM.step, Iterator.step]; rfl

theorem _root_.List.step_iterM {l : List β} :
    (l.iterM m).step = match l with
      | [] => pure (.deflate ⟨.done, rfl⟩)
      | x :: xs => pure (.deflate ⟨.yield (xs.iterM m) x, rfl⟩) := by
  cases l <;> simp [List.step_iterM_cons, List.step_iterM_nil]

theorem ListIterator.toArrayMapped_iterM [Monad n] [LawfulMonad n]
    {β : Type w} {γ : Type w} {lift : ⦃δ : Type w⦄ → m δ → n δ}
    [LawfulMonadLiftFunction lift] {f : β → n γ} {l : List β} :
    IteratorCollect.toArrayMapped lift f (l.iterM m) (m := m) = List.toArray <$> l.mapM f := by
  rw [LawfulIteratorCollect.toArrayMapped_eq]
  induction l with
  | nil =>
    rw [IterM.DefaultConsumers.toArrayMapped_eq_match_step]
    simp [List.step_iterM_nil, LawfulMonadLiftFunction.lift_pure]
  | cons x xs ih =>
    rw [IterM.DefaultConsumers.toArrayMapped_eq_match_step]
    simp [List.step_iterM_cons, List.mapM_cons, pure_bind, ih, LawfulMonadLiftFunction.lift_pure]

@[simp]
theorem _root_.List.toArray_iterM [LawfulMonad m] {l : List β} :
    (l.iterM m).toArray = pure l.toArray := by
  simp only [IterM.toArray, ListIterator.toArrayMapped_iterM]
  rw [List.mapM_pure, map_pure, List.map_id']

@[simp]
theorem _root_.List.toList_iterM [LawfulMonad m] {l : List β} :
    (l.iterM m).toList = pure l := by
  rw [← IterM.toList_toArray, List.toArray_iterM, map_pure, List.toList_toArray]

@[simp]
theorem _root_.List.toListRev_iterM [LawfulMonad m] {l : List β} :
    (l.iterM m).toListRev = pure l.reverse := by
  simp [IterM.toListRev_eq, List.toList_iterM]

end Std.Iterators
