/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
prelude
import Std.Data.Iterators.Producers.Monadic.Array
import Std.Data.Iterators.Consumers
import Std.Data.Iterators.Lemmas.Consumers.Monadic
import Std.Data.Internal.LawfulMonadLiftFunction

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

@[simp]
theorem _root_.Array.toList_iterFromIdxM [LawfulMonad m] {array : Array β}
    {pos : Nat} :
    (array.iterFromIdxM m pos).toList = pure (array.toList.drop pos) := by
  by_cases h : pos < array.size
  · suffices h' : ∀ n p, p ≥ array.size - n → (array.iterFromIdxM m p).toList = pure (array.toList.drop p) by
      apply h' array.size
      omega
    intro n
    induction n
    · intro p hp
      rw [IterM.toList_eq_match_step]
      simp [Array.step_iterFromIdxM]
      rw [List.drop_eq_nil_iff.mpr]
      · simp [show ¬ p < array.size by omega]
      · simp only [Array.length_toList]
        omega
    · rename_i n ih
      intro p hp
      by_cases h : p ≥ array.size - n
      · apply ih
        assumption
      · rw [IterM.toList_eq_match_step, Array.step_iterFromIdxM]
        simp [show p < array.size by omega]
        rw [ih _ (by omega)]
        simp
        apply congrArg pure
        rw (occs := [2]) [← List.getElem_cons_drop_succ_eq_drop]
        simp
        rw [Array.getElem_toList]
  · rw [IterM.toList_eq_match_step, List.drop_eq_nil_iff.mpr]
    · simp [Array.step_iterFromIdxM, h]
    · simp only [Array.length_toList]
      omega

@[simp]
theorem _root_.Array.toList_iterM [LawfulMonad m] {array : Array β} :
    (array.iterM m).toList = pure array.toList := by
  simp [Array.iterM_eq_iterFromIdxM, Array.toList_iterFromIdxM]

-- TODO: Init.Data.Array.Lemmas (also used this in Std.Data.Iterators.Lemmas.Combinators.Drop)
private theorem _root_.List.drop_toArray' {l : List α} {k : Nat} :
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
  rw [List.drop_toArray']

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
