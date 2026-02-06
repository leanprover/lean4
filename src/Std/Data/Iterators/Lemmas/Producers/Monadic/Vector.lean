/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Lemmas.Producers.Monadic.Array
public import Std.Data.Iterators.Producers.Monadic.Vector
public import Std.Data.Iterators.Lemmas.Consumers.Monadic
public import Std.Data.Iterators.Lemmas.Producers.Monadic.List
public import Init.Data.Array.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.TakeDrop
import Init.Omega
import Init.Data.Vector.Lemmas

set_option doc.verso true

open Std Std.Iterators

@[expose] public section

/-!
# Lemmas about vector iterators

This module provides lemmas about the interactions of {name}`Vector.iterM` with {name}`IterM.step`
and various
collectors.
-/

variable {m : Type w → Type w'} [Monad m] {β : Type w} {n : Nat}

theorem Vector.iterM_eq_iterFromIdxM {xs : Vector β n} :
    xs.iterM m = xs.iterFromIdxM m 0 :=
  rfl

theorem Std.Iterators.Vector.isPlausibleStep_iterFromIdxM_of_lt {xs : Vector β n} {pos : Nat}
    (h : pos < n) :
    (xs.iterFromIdxM m pos).IsPlausibleStep (.yield (xs.iterFromIdxM m (pos + 1)) xs[pos]) := by
  simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep]
  refine ⟨rfl, rfl, ?_, rfl⟩
  simpa [Vector.iterFromIdxM, Array.iterFromIdxM] using h

theorem Std.Iterators.Vector.isPlausibleStep_iterFromIdxM_of_not_lt {xs : Vector β n} {pos : Nat}
    (h : ¬ pos < n) :
    (xs.iterFromIdxM m pos).IsPlausibleStep .done := by
  simp only [IterM.IsPlausibleStep, Iterator.IsPlausibleStep]
  simpa [Vector.iterFromIdxM, Array.iterFromIdxM, Nat.not_lt] using h

theorem Std.Iterators.Vector.isPlausibleStep_iterM_of_pos {xs : Vector β n}
    (h : 0 < n) :
    (xs.iterM m).IsPlausibleStep (.yield (xs.iterFromIdxM m 1) xs[0]) := by
  simp only [Vector.iterM_eq_iterFromIdxM]
  exact isPlausibleStep_iterFromIdxM_of_lt h

theorem Std.Iterators.Vector.isPlausibleStep_iterM_of_not_pos {xs : Vector β n}
    (h : ¬ 0 < n) :
    (xs.iterM m).IsPlausibleStep .done := by
  simp only [Vector.iterM_eq_iterFromIdxM]
  exact isPlausibleStep_iterFromIdxM_of_not_lt h

@[simp, grind =]
theorem Vector.iterFromIdxM_toArray {xs : Vector β n} {pos : Nat} :
    xs.toArray.iterFromIdxM m pos = xs.iterFromIdxM m pos :=
  rfl

@[simp, grind =]
theorem Vector.iterM_toArray {xs : Vector β n} :
    xs.toArray.iterM m = xs.iterM m :=
  rfl

theorem Vector.step_iterFromIdxM {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdxM m pos).step = (pure <| .deflate <| if h : pos < n then
        .yield
          (xs.iterFromIdxM m (pos + 1))
          xs[pos]
          (Vector.isPlausibleStep_iterFromIdxM_of_lt h)
      else
        .done (Vector.isPlausibleStep_iterFromIdxM_of_not_lt h)) := by
  simp [← Vector.iterFromIdxM_toArray, Array.step_iterFromIdxM]

theorem Vector.step_iterM {xs : Vector β n} :
    (xs.iterM m).step = (pure <| .deflate <| if h : 0 < n then
        .yield
          (xs.iterFromIdxM m 1)
          xs[0]
          (Vector.isPlausibleStep_iterM_of_pos h)
      else
        .done (Vector.isPlausibleStep_iterM_of_not_pos h)) := by
  simp [← Vector.iterFromIdxM_toArray, ← Vector.iterM_toArray, Array.step_iterM]

section Equivalence

theorem Vector.iterFromIdxM_equiv_iterM_drop_toList {α : Type w} {xs : Vector α n}
    {m : Type w → Type w'} [Monad m] [LawfulMonad m] {pos : Nat} :
    (xs.iterFromIdxM m pos).Equiv ((xs.toList.drop pos).iterM m) := by
  simp only [← Vector.iterFromIdxM_toArray]
  apply Array.iterFromIdxM_equiv_iterM_drop_toList

theorem Vector.iterM_equiv_iterM_toList {α : Type w} {xs : Vector α n} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] :
    (xs.iterM m).Equiv (xs.toList.iterM m) := by
  simp only [← Vector.iterM_toArray]
  apply Array.iterM_equiv_iterM_toList

end Equivalence

@[simp, grind =]
theorem Vector.toList_iterFromIdxM [LawfulMonad m] {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdxM m pos).toList = pure (xs.toList.drop pos) := by
  simp [← Vector.iterFromIdxM_toArray, Vector.toList_toArray]

@[simp, grind =]
theorem Vector.toList_iterM [LawfulMonad m] {xs : Vector β n} :
    (xs.iterM m).toList = pure xs.toList := by
  simp [← Vector.iterM_toArray, Vector.toList_toArray]

@[simp, grind =]
theorem Vector.toArray_iterFromIdxM [LawfulMonad m] {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdxM m pos).toArray = pure (xs.toArray.extract pos n) := by
  simp [← Vector.iterFromIdxM_toArray]

@[simp, grind =]
theorem Vector.toArray_iterM [LawfulMonad m] {xs : Vector β n} :
    (xs.iterM m).toArray = pure xs.toArray := by
  simp [← Vector.iterM_toArray]

@[simp, grind =]
theorem Vector.toListRev_iterFromIdxM [LawfulMonad m] {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdxM m pos).toListRev = pure (xs.toList.drop pos).reverse := by
  simp [← Vector.iterFromIdxM_toArray, Vector.toList_toArray]

@[simp, grind =]
theorem Vector.toListRev_toIterM [LawfulMonad m] {xs : Vector β n} :
    (xs.iterM m).toListRev = pure xs.toList.reverse := by
  simp [← Vector.iterM_toArray, Vector.toList_toArray]

@[simp, grind =]
theorem Vector.length_iterFromIdxM [LawfulMonad m] {xs : Vector β n} {pos : Nat} :
    (xs.iterFromIdxM m pos).length = pure (.up (n - pos)) := by
  simp [← IterM.up_length_toList_eq_length]

@[simp, grind =]
theorem Vector.length_iterM [LawfulMonad m] {xs : Vector β n} :
    (xs.iterM m).length = pure (.up n) := by
  simp [← IterM.up_length_toList_eq_length]
