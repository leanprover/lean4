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

/-- Insert an element into an array, after the last element which is not `lt` the inserted element. -/
def orderedInsert (a : Array α) (x : α) (lt : α → α → Bool := by exact (· < ·)) : Array α :=
  insertionSort.swapLoop lt ⟨a.push x, rfl⟩ a.size (by simp) |>.toArray

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
      rw [← Vector.push_swap, ih, if_pos h]
    · rw [Vector.getElem_push_lt (by omega), Vector.getElem_push_lt (by omega)] at h
      rw [if_neg h]

theorem swapLoop_cast {n m} (a : Vector α n) (j : Nat) (h : j < n) (h : n = m) :
    insertionSort.swapLoop lt (a.cast h) j = (insertionSort.swapLoop lt a j).cast h := by
  subst h
  simp

theorem insertionSort_push (a : Array α) (x : α) :
    (a.push x).insertionSort lt =
      (insertionSort.swapLoop lt ⟨(a.insertionSort lt).push x, rfl⟩ a.size (by simp)).toArray := by
  rw [insertionSort]
  rw [Nat.fold_congr (size_push a x)]
  rw [Nat.fold]
  have : (a.size.fold (fun i h acc => insertionSort.swapLoop lt acc i (by simp; omega)) ⟨a.push x, rfl⟩) =
      ((a.size.fold (fun i h acc => insertionSort.swapLoop lt acc i h) ⟨a, rfl⟩).push x).cast (by simp) := by
    sorry
  rw [this]
  simp [swapLoop_cast]
  unfold insertionSort
  simp [Vector.push]
  congr
  all_goals simp

end Array
