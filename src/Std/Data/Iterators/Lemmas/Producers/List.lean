/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Iterators.Consumers
import Init.Data.Iterators.Lemmas.Consumers.Collect
import Std.Data.Iterators.Producers.List
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
theorem _root_.List.toArray_iter {l : List β} :
    l.iter.toArray = l.toArray := by
  simp [List.iter, List.toArray_iterM, Iter.toArray_eq_toArray_toIterM]

@[simp]
theorem _root_.List.toList_iter {l : List β} :
    l.iter.toList = l := by
  simp [List.iter, List.toList_iterM]

@[simp]
theorem _root_.List.toListRev_iter {l : List β} :
    l.iter.toListRev = l.reverse := by
  simp [List.iter, Iter.toListRev_eq_toListRev_toIterM, List.toListRev_iterM]

end Std.Iterators
