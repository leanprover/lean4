/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Std.Data.Iterators.Producers.Monadic.Array
public import Std.Data.Iterators.Lemmas.Consumers.Monadic
public import Std.Data.Iterators.Lemmas.Producers.Monadic.List

@[expose] public section

/-!
# Lemmas about array iterators

This module provides lemmas about the interactions of `Array.iterM` with `IterM.step` and various
collectors.
-/

open Std Std.Iterators Std.Iterators.Types

variable {m : Type w → Type w'} [Monad m] {β : Type w}

theorem Array.iterM_eq_iterFromIdxM {array : Array β} :
    array.iterM m = array.iterFromIdxM m 0 :=
  rfl

theorem Array.step_iterFromIdxM {array : Array β} {pos : Nat} :
    (array.iterFromIdxM m pos).step = (pure <| .deflate <| if h : pos < array.size then
        .yield
          (array.iterFromIdxM m (pos + 1))
          array[pos]
          ⟨rfl, rfl, h, rfl⟩
      else
        .done (Nat.not_lt.mp h)) := by
  rfl

theorem Array.step_iterM {array : Array β} :
    (array.iterM m).step = (pure <| .deflate <| if h : 0 < array.size then
        .yield
          (array.iterFromIdxM m 1)
          array[0]
          ⟨rfl, rfl, h, rfl⟩
      else
        .done (Nat.not_lt.mp h)) := by
  rfl

section Equivalence

theorem Std.Iterators.Types.ArrayIterator.stepAsHetT_iterFromIdxM [LawfulMonad m] {array : Array β}
    {pos : Nat} :
    (array.iterFromIdxM m pos).stepAsHetT = (if _ : pos < array.size then
      pure (.yield (array.iterFromIdxM m (pos + 1)) array[pos])
    else
      pure .done) := by
  simp only [Array.iterFromIdxM, IterM.mk, pure, HetT.ext_iff, Equivalence.property_step,
    IterM.IsPlausibleStep, Iterator.IsPlausibleStep, Equivalence.prun_step, ge_iff_le]
  refine ⟨?_, ?_⟩
  · ext step
    cases step
    · dsimp only
      split
      · simp only [HetT.property_pure, IterStep.yield.injEq, IterM.ext_iff, ArrayIterator.ext_iff]
        constructor
        · rintro ⟨rfl, h, h', rfl⟩
          exact ⟨⟨rfl, h.symm⟩, rfl⟩
        · rintro ⟨⟨rfl, h⟩, rfl⟩
          exact ⟨rfl, h.symm, ‹_›, rfl⟩
      · simp only [HetT.property_pure, reduceCtorEq, iff_false, not_and, not_exists]
        omega
    · dsimp only
      split <;> simp
    · dsimp only
      split <;> simp only [HetT.property_pure, reduceCtorEq, iff_false, Nat.not_le, iff_true] <;>
        omega
  · intro β f
    simp [IterM.step, Iterator.step]
    split <;> simp

theorem Array.iterFromIdxM_equiv_iterM_drop_toList {α : Type w} {array : Array α}
    {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] {pos : Nat} :
    (array.iterFromIdxM m pos).Equiv ((array.toList.drop pos).iterM m) := by
  conv =>
    rhs
    rw [show pos = (array.iterFromIdxM m pos).internalState.pos from rfl]
    rw (occs := [2]) [show array = (array.iterFromIdxM m pos).internalState.array from rfl]
  generalize array.iterFromIdxM m pos = it
  apply IterM.Equiv.of_morphism
  intro it
  match it with
  | Array.iterFromIdxM array _ pos =>
    rw [ArrayIterator.stepAsHetT_iterFromIdxM, Types.ListIterator.stepAsHetT_iterM]
    simp [Array.iterFromIdxM, IterM.mk]
    rw [show array = array.toList.toArray from Array.toArray_toList]
    generalize array.toList = l
    simp [Functor.map]
    split
    · rename_i heq
      rw [List.drop_eq_nil_iff] at heq
      rw [dif_neg (by omega)]
      simp [Pure.pure, HetT.pure_bind]
    · rename_i x xs heq
      have hlt : pos < l.length := by
        have := heq ▸ List.drop_eq_nil_iff
        simpa using this
      rw [dif_pos hlt]
      simp [Pure.pure]
      congr
      · rw [← List.drop_drop (i := 1) (j := pos), heq, List.drop_succ_cons, List.drop_zero]
      · have:= List.getElem_drop' (xs := l) (i := pos) (j := 0)
        simp only [Nat.add_zero, heq, List.getElem_cons_zero] at this
        exact (this hlt).symm

theorem Array.iterM_equiv_iterM_toList {α : Type w} {array : Array α} {m : Type w → Type w'}
    [Monad m] [LawfulMonad m] :
    (array.iterM m).Equiv (array.toList.iterM m) := by
  rw [Array.iterM_eq_iterFromIdxM]
  simpa using iterFromIdxM_equiv_iterM_drop_toList

end Equivalence

@[simp, grind =]
theorem Array.toList_iterFromIdxM [LawfulMonad m] {array : Array β}
    {pos : Nat} :
    (array.iterFromIdxM m pos).toList = pure (array.toList.drop pos) := by
  simp [Array.iterFromIdxM_equiv_iterM_drop_toList.toList_eq]

@[simp, grind =]
theorem Array.toList_iterM [LawfulMonad m] {array : Array β} :
    (array.iterM m).toList = pure array.toList := by
  simp [Array.iterM_eq_iterFromIdxM, Array.toList_iterFromIdxM]

@[simp, grind =]
theorem Array.toArray_iterFromIdxM [LawfulMonad m] {array : Array β} {pos : Nat} :
    (array.iterFromIdxM m pos).toArray = pure (array.extract pos) := by
  simp [← IterM.toArray_toList, Array.toList_iterFromIdxM]
  rw (occs := [2]) [← Array.toArray_toList (xs := array)]
  rw [← List.toArray_drop]

@[simp, grind =]
theorem Array.toArray_toIterM [LawfulMonad m] {array : Array β} :
    (array.iterM m).toArray = pure array := by
  simp [Array.iterM_eq_iterFromIdxM, Array.toArray_iterFromIdxM]

@[simp, grind =]
theorem Array.toListRev_iterFromIdxM [LawfulMonad m] {array : Array β} {pos : Nat} :
    (array.iterFromIdxM m pos).toListRev = pure (array.toList.drop pos).reverse := by
  simp [IterM.toListRev_eq, Array.toList_iterFromIdxM]

@[simp, grind =]
theorem Array.toListRev_toIterM [LawfulMonad m] {array : Array β} :
    (array.iterM m).toListRev = pure array.toListRev := by
  simp [Array.iterM_eq_iterFromIdxM, Array.toListRev_iterFromIdxM]
