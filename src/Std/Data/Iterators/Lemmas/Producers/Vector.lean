/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Lemmas.Producers.Array
public import Std.Data.Iterators.Producers.Vector
public import Std.Data.Iterators.Producers.Monadic.Vector
import Init.Data.Vector.Lemmas
import Std.Data.Iterators.Lemmas.Consumers.Collect
import Std.Data.Iterators.Lemmas.Consumers.Loop
import Init.Data.List.TakeDrop
import Std.Data.Iterators.Lemmas.Producers.Monadic.Vector

set_option doc.verso true

open Std Std.Iterators

@[expose] public section

/-!
# Lemmas about vector iterators

This module provides lemmas about the interactions of {name}`Vector.iter` with {name}`Iter.step` and
various collectors.
-/

variable {β : Type w} {n : Nat}

theorem Vector.iter_eq_toIter_iterM {xs : Vector β n} :
    xs.iter = (xs.iterM Id).toIter :=
  rfl

theorem Vector.iter_eq_iterFromIdx {xs : Vector β n} :
    xs.iter = xs.iterFromIdx 0 :=
  rfl

theorem Vector.iterFromIdx_eq_toIter_iterFromIdxM {xs : Vector β n} {pos : Nat} :
    xs.iterFromIdx pos = (xs.iterFromIdxM Id pos).toIter :=
  rfl

theorem Std.Iterators.Vector.isPlausibleStep_iterFromIdx_of_lt {xs : Vector β n} {pos : Nat}
    (h : pos < n) :
    (xs.iterFromIdx pos).IsPlausibleStep (.yield (xs.iterFromIdx (pos + 1)) xs[pos]) := by
  simp only [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep]
  refine ⟨rfl, rfl, ?_, rfl⟩
  simpa [Vector.iterFromIdx, Array.iterFromIdxM, Array.iterFromIdx] using h

theorem Std.Iterators.Vector.isPlausibleStep_iterFromIdx_of_not_lt {xs : Vector β n} {pos : Nat}
    (h : ¬ pos < n) :
    (xs.iterFromIdx pos).IsPlausibleStep .done := by
  simp only [Iter.IsPlausibleStep, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Types.ArrayIterator.instIterator]
  simpa [Vector.iterFromIdx, Array.iterFromIdxM, Array.iterFromIdx, Nat.not_lt] using h

theorem Std.Iterators.Vector.isPlausibleStep_iter_of_pos {xs : Vector β n}
    (h : 0 < n) :
    (xs.iter).IsPlausibleStep (.yield (xs.iterFromIdx 1) xs[0]) := by
  simp only [Vector.iter_eq_iterFromIdx]
  exact isPlausibleStep_iterFromIdx_of_lt h

theorem Std.Iterators.Vector.isPlausibleStep_iter_of_not_pos {xs : Vector β n}
    (h : ¬ 0 < n) :
    (xs.iter).IsPlausibleStep .done := by
  simp only [Vector.iter_eq_iterFromIdx]
  exact isPlausibleStep_iterFromIdx_of_not_lt h

@[simp, grind =]
theorem Vector.iterFromIdx_toArray {xs : Vector β n} {pos : Nat} :
    xs.toArray.iterFromIdx pos = xs.iterFromIdx pos :=
  rfl

@[simp, grind =]
theorem Vector.iter_toArray {xs : Vector β n} :
    xs.toArray.iter = xs.iter :=
  rfl

theorem Vector.step_iterFromIdx {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdx pos).step = if h : pos < n then
        .yield
          (xs.iterFromIdx (pos + 1))
          xs[pos]
          (Vector.isPlausibleStep_iterFromIdx_of_lt h)
      else
        .done (Vector.isPlausibleStep_iterFromIdx_of_not_lt h) := by
  split <;> simp [Vector.iterFromIdx_eq_toIter_iterFromIdxM, Iter.step, Vector.step_iterFromIdxM, *]

theorem Vector.step_iter {xs : Vector β n} :
    xs.iter.step = if h : 0 < n then
        .yield
          (xs.iterFromIdx 1)
          xs[0]
          (Vector.isPlausibleStep_iter_of_pos h)
      else
        .done (Vector.isPlausibleStep_iter_of_not_pos h) := by
  simp [iter_eq_iterFromIdx, step_iterFromIdx]

@[simp, grind =]
theorem Vector.toList_iterFromIdx {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdx pos).toList = xs.toList.drop pos := by
  simp [Iter.toList, Vector.iterFromIdx_eq_toIter_iterFromIdxM, Iter.toIterM_toIter,
    Vector.toList_iterFromIdxM]

@[simp, grind =]
theorem Vector.toList_iter {xs : Vector β n} :
    xs.iter.toList = xs.toList := by
  simp [← iter_toArray, Vector.toList_toArray]

@[simp, grind =]
theorem Vector.toArray_iterFromIdx {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdx pos).toArray = xs.toArray.extract pos n := by
  simp [← iterFromIdx_toArray]

@[simp, grind =]
theorem Vector.toArray_iter {xs : Vector β n} :
    xs.iter.toArray = xs.toArray := by
  simp [← iter_toArray]

@[simp, grind =]
theorem Vector.toListRev_iterFromIdx {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdx pos).toListRev = (xs.toList.drop pos).reverse := by
  simp [Iter.toListRev_eq, Vector.toList_iterFromIdx]

@[simp, grind =]
theorem Vector.toListRev_toIter {xs : Vector β n} :
    xs.iter.toListRev = xs.toList.reverse := by
  simp [Vector.iter_eq_iterFromIdx]

@[simp, grind =]
theorem Vector.length_iterFromIdx {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdx pos).length = n - pos := by
  simp [← Iter.length_toList_eq_length]

@[simp, grind =]
theorem Vector.length_iter {xs : Vector β n} :
    xs.iter.length = n := by
  simp [← Iter.length_toList_eq_length]

section Equivalence

theorem Vector.iterFromIdx_equiv_iter_drop_toList {α : Type w} {xs : Vector α n}
    {pos : Nat} : (xs.iterFromIdx pos).Equiv (xs.toList.drop pos).iter := by
  apply IterM.Equiv.toIter
  exact Vector.iterFromIdxM_equiv_iterM_drop_toList

theorem Vector.iter_equiv_iter_toList {α : Type w} {xs : Vector α n} :
    xs.iter.Equiv xs.toList.iter := by
  rw [Vector.iter_eq_iterFromIdx]
  simpa using iterFromIdx_equiv_iter_drop_toList

end Equivalence
