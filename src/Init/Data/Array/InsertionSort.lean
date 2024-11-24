/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Nat.Fold
import Init.Data.Vector.Lemmas


namespace Array

@[inline] def insertionSort (a : Array α) (lt : α → α → Bool := by exact (· < ·)) : Array α :=
  a.size.fold (init := ⟨a, rfl⟩) (f := fun i h acc => swapLoop acc i h) |>.toArray
where
  @[specialize] swapLoop {n} (a : Vector α n) (j : Nat) (h : j < n := by get_elem_tactic) : Vector α n :=
    match h' : j with
    | 0    => a
    | j'+1 =>
      if lt a[j] a[j'] then
        swapLoop (a.swap j j') j'
      else
        a

@[simp] theorem size_insertionSort (a : Array α) : (a.insertionSort lt).size = a.size := by
  simp [insertionSort]

theorem insertionSort_swapLoop_push {n} (a : Vector α n) (x : α) (j : Nat) (h : j < n) :
    insertionSort.swapLoop lt (a.push x) j = (insertionSort.swapLoop lt a j).push x := by
  induction j generalizing a with
  | zero => simp [insertionSort.swapLoop]
  | succ j ih =>
    simp [insertionSort.swapLoop]
    split <;> rename_i h
    · rw [Vector.getElem_push_lt (by omega), Vector.getElem_push_lt (by omega)] at h
      rw [Vector.swap_push]
      simp [h]

    · sorry


end Array
