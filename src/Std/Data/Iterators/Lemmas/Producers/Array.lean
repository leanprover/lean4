/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Lemmas.Consumers.Collect
import Std.Data.Iterators.Producers.Array
import Std.Data.Iterators.Producers.List
import Std.Data.Iterators.Lemmas.Producers.Monadic.Array

/-!
# Lemmas about array iterators

This module provides lemmas about the interactions of `Array.iter` with `Iter.step` and various
collectors.
-/

namespace Std.Iterators

variable {β : Type w}

theorem _root_.Array.iter_eq_toIter_iterM {array : Array β} :
    array.iter = (array.iterM Id).toIter :=
  rfl

theorem _root_.Array.iter_eq_iterFromIdx {array : Array β} :
    array.iter = array.iterFromIdx 0 :=
  rfl

theorem _root_.Array.iterFromIdx_eq_toIter_iterFromIdxM {array : Array β} {pos : Nat} :
    array.iterFromIdx pos = (array.iterFromIdxM Id pos).toIter :=
  rfl

theorem _root_.Array.step_iterFromIdx {array : Array β} {pos : Nat} :
    (array.iterFromIdx pos).step = if h : pos < array.size then
        .yield
          (array.iterFromIdx (pos + 1))
          array[pos]
          ⟨rfl, rfl, h, rfl⟩
      else
        .done (Nat.not_lt.mp h) := by
  simp only [Array.iterFromIdx_eq_toIter_iterFromIdxM, Iter.step, Iter.toIterM_toIter,
    Array.step_iterFromIdxM, Id.run_pure]
  split <;> rfl

theorem _root_.Array.step_iter {array : Array β} :
    array.iter.step = if h : 0 < array.size then
        .yield
          (array.iterFromIdx 1)
          array[0]
          ⟨rfl, rfl, h, rfl⟩
      else
        .done (Nat.not_lt.mp h) := by
  simp only [Array.iter_eq_iterFromIdx, Array.step_iterFromIdx]

@[simp]
theorem _root_.Array.toList_iterFromIdx {array : Array β}
    {pos : Nat} :
    (array.iterFromIdx pos).toList = array.toList.drop pos := by
  simp [Iter.toList, Array.iterFromIdx_eq_toIter_iterFromIdxM, Iter.toIterM_toIter,
    Array.toList_iterFromIdxM]

@[simp]
theorem _root_.Array.toList_iter {array : Array β} :
    array.iter.toList = array.toList := by
  simp [Array.iter_eq_iterFromIdx, Array.toList_iterFromIdx]

@[simp]
theorem _root_.Array.toArray_iterFromIdx {array : Array β} {pos : Nat} :
    (array.iterFromIdx pos).toArray = array.extract pos := by
  simp [Array.iterFromIdx_eq_toIter_iterFromIdxM, Iter.toArray]

@[simp]
theorem _root_.Array.toArray_toIter {array : Array β} :
    array.iter.toArray = array := by
  simp [Array.iter_eq_iterFromIdx]

@[simp]
theorem _root_.Array.toListRev_iterFromIdx {array : Array β} {pos : Nat} :
    (array.iterFromIdx pos).toListRev = (array.toList.drop pos).reverse := by
  simp [Iter.toListRev_eq, Array.toList_iterFromIdx]

@[simp]
theorem _root_.Array.toListRev_toIter {array : Array β} :
    array.iter.toListRev = array.toListRev := by
  simp [Array.iter_eq_iterFromIdx]

section Equivalence

theorem Array.iterFromIdx_equiv_iter_drop_toList {α : Type w} {array : Array α}
    {pos : Nat} : (array.iterFromIdx pos).Equiv (array.toList.drop pos).iter := by
  apply IterM.Equiv.toIter
  exact iterFromIdxM_equiv_iterM_drop_toList

theorem Array.iter_equiv_iter_toList {α : Type w} {array : Array α} :
    array.iter.Equiv array.toList.iter := by
  rw [Array.iter_eq_iterFromIdx]
  simpa using iterFromIdx_equiv_iter_drop_toList

end Equivalence

end Std.Iterators
