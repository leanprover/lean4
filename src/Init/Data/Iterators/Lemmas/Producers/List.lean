/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Iterators.Lemmas.Consumers.Collect
public import Init.Data.Iterators.Producers.List
public import Init.Data.Iterators.Lemmas.Producers.Monadic.List

@[expose] public section

/-!
# Lemmas about list iterators

This module provides lemmas about the interactions of `List.iter` with `Iter.step` and various
collectors.
-/

open Std Std.Iterators

variable {β : Type w}

@[simp]
theorem List.step_iter_nil :
    (([] : List β).iter).step = ⟨.done, rfl⟩ := by
  simp [Iter.step, IterM.step, Iterator.step, List.iter, List.iterM, IterM.mk]

@[simp]
theorem List.step_iter_cons {x : β} {xs : List β} :
    ((x :: xs).iter).step = ⟨.yield xs.iter x, rfl⟩ := by
  simp [List.iter, List.iterM, IterM.mk, IterM.toIter, Iter.step, Iter.toIterM, IterM.step,
    Iterator.step]

@[simp, grind =]
theorem List.toArray_iter {l : List β} :
    l.iter.toArray = l.toArray := by
  simp [List.iter, List.toArray_iterM, Iter.toArray_eq_toArray_toIterM]

@[simp, grind =]
theorem List.toList_iter {l : List β} :
    l.iter.toList = l := by
  simp [List.iter, List.toList_iterM]

@[simp, grind =]
theorem List.toListRev_iter {l : List β} :
    l.iter.toListRev = l.reverse := by
  simp [List.iter, Iter.toListRev_eq_toListRev_toIterM, List.toListRev_iterM]
