/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Consumers
import Std.Data.Iterators.Lemmas.Producers.Monadic.List

/-!
# Lemmas about list iterators

This module provides lemmas about the interactions of `List.iter` with `Iter.step` and various
collectors.
-/

namespace Std.Iterators

variable {β : Type w}

@[simp]
theorem _root_.List.step_iter_nil :
    (([] : List β).iter).step = ⟨.done, rfl⟩ := by
  simp only [Iter.step, IterM.step, Iterator.step]; rfl

@[simp]
theorem _root_.List.step_iter_cons {x : β} {xs : List β} :
    ((x :: xs).iter).step = ⟨.yield xs.iter x, rfl⟩ := by
  simp only [List.iter, List.iterM, IterM.step, Iterator.step]; rfl

@[simp]
theorem _root_.List.toArray_iter {m : Type w → Type w'} [Monad m] [LawfulMonad m] {l : List β} :
    (l.iterM m).toArray = pure l.toArray := by
  simp only [IterM.toArray, ListIterator.toArrayMapped_toIterM]
  rw [List.mapM_pure, map_pure, List.map_id']

@[simp]
theorem _root_.List.toList_iter {m : Type w → Type w'} [Monad m] [LawfulMonad m] {l : List β} :
    (l.iterM m).toList = pure l := by
  rw [← IterM.toList_toArray, List.toArray_iterM, map_pure, List.toList_toArray]

@[simp]
theorem _root_.List.toListRev_iter {m : Type w → Type w'} [Monad m] [LawfulMonad m] {l : List β} :
    (l.iterM m).toListRev = pure l.reverse := by
  simp [IterM.toListRev_eq, List.toList_iterM]

end Std.Iterators
