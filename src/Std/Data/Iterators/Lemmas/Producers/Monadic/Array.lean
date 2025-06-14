/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Init.Data.Iterators.Internal.LawfulMonadLiftFunction
import Init.Data.Iterators.Consumers
import Std.Data.Iterators.Producers.Monadic.Array
import Std.Data.Iterators.Lemmas.Consumers.Monadic
import Std.Data.Iterators.Lemmas.Producers.Monadic.List
import Std.Data.Iterators.Lemmas.Equivalence.Basic

/-!
# Lemmas about array iterators

This module provides lemmas about the interactions of `Array.iterM` with `IterM.step` and various
collectors.
-/

namespace Std.Iterators

variable {m : Type w → Type w'} [Monad m] {β : Type w}

theorem _root_.Array.iterM_eq_iterFromIdxM {array : Array β} :
    array.iterM m = array.iterFromIdxM m 0 :=
  rfl

theorem _root_.Array.step_iterFromIdxM {array : Array β} {pos : Nat} :
    (array.iterFromIdxM m pos).step = (pure <| if h : pos < array.size then
        .yield
          (array.iterFromIdxM m (pos + 1))
          array[pos]
          ⟨rfl, rfl, h, rfl⟩
      else
        .done (Nat.not_lt.mp h)) := by
  rfl

theorem _root_.Array.step_iterM {array : Array β} :
    (array.iterM m).step = (pure <| if h : 0 < array.size then
        .yield
          (array.iterFromIdxM m 1)
          array[0]
          ⟨rfl, rfl, h, rfl⟩
      else
        .done (Nat.not_lt.mp h)) := by
  rfl

section Equivalence

theorem ArrayIterator.stepAsHetT_iterFromIdxM [LawfulMonad m] {array : Array β} {pos : Nat} :
  (array.iterFromIdxM m pos).stepAsHetT = (if _ : pos < array.size then
      pure (.yield (array.iterFromIdxM m (pos + 1)) array[pos])
    else
      pure .done) := by
  simp only [Array.iterFromIdxM, toIterM, pure, HetT.ext_iff, Equivalence.property_step,
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
    rw [ArrayIterator.stepAsHetT_iterFromIdxM, ListIterator.stepAsHetT_iterM]
    simp [Array.iterFromIdxM, toIterM]
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

@[simp]
theorem _root_.Array.toList_iterFromIdxM [LawfulMonad m] {array : Array β}
    {pos : Nat} :
    (array.iterFromIdxM m pos).toList = pure (array.toList.drop pos) := by
  simp [Array.iterFromIdxM_equiv_iterM_drop_toList.toList_eq]

@[simp]
theorem _root_.Array.toList_iterM [LawfulMonad m] {array : Array β} :
    (array.iterM m).toList = pure array.toList := by
  simp [Array.iterM_eq_iterFromIdxM, Array.toList_iterFromIdxM]

-- Move to Init.Data.Array.Lemmas in a separate PR afterwards
private theorem drop_toArray' {l : List α} {k : Nat} :
    l.toArray.drop k = (l.drop k).toArray := by
  induction l generalizing k
  case nil => simp
  case cons l' ih =>
    match k with
    | 0 => simp
    | k' + 1 => simp [List.drop_succ_cons, ← ih]

@[simp]
theorem _root_.Array.toArray_iterFromIdxM [LawfulMonad m] {array : Array β} {pos : Nat} :
    (array.iterFromIdxM m pos).toArray = pure (array.extract pos) := by
  simp [← IterM.toArray_toList, Array.toList_iterFromIdxM]
  rw [← Array.drop_eq_extract]
  rw (occs := [2]) [← Array.toArray_toList (xs := array)]
  rw [drop_toArray']

@[simp]
theorem _root_.Array.toArray_toIterM [LawfulMonad m] {array : Array β} :
    (array.iterM m).toArray = pure array := by
  simp [Array.iterM_eq_iterFromIdxM, Array.toArray_iterFromIdxM]

@[simp]
theorem _root_.Array.toListRev_iterFromIdxM [LawfulMonad m] {array : Array β} {pos : Nat} :
    (array.iterFromIdxM m pos).toListRev = pure (array.toList.drop pos).reverse := by
  simp [IterM.toListRev_eq, Array.toList_iterFromIdxM]

@[simp]
theorem _root_.Array.toListRev_toIterM [LawfulMonad m] {array : Array β} :
    (array.iterM m).toListRev = pure array.toListRev := by
  simp [Array.iterM_eq_iterFromIdxM, Array.toListRev_iterFromIdxM]

end Std.Iterators
