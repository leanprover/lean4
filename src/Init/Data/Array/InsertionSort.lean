/-
Copyright (c) 2018 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Nat.Fold
import Init.Data.Vector.Lemmas

namespace Vector

/-- Swap the `i`-th element repeatedly to the left, while the element to its left is not `lt` it. -/
@[specialize, inline] def swapLeftWhileLT {n} (a : Vector α n) (i : Nat) (h : i < n)
    (lt : α → α → Bool := by exact (· < ·)) : Vector α n :=
  match h' : i with
  | 0 => a
  | i'+1 =>
    if lt a[i'] a[i] then
      a
    else
      swapLeftWhileLT (a.swap i' i) i' (by omega) lt

end Vector

open Vector
namespace Array

/-- Sort an array in place using insertion sort. -/
@[inline] def insertionSort (a : Array α) (lt : α → α → Bool := by exact (· < ·)) : Array α :=
  a.size.fold (init := ⟨a, rfl⟩) (f := fun i h acc => swapLeftWhileLT acc i h lt) |>.toArray

/-- Insert an element into an array, after the last element which is not `lt` the inserted element. -/
def orderedInsert (a : Array α) (x : α) (lt : α → α → Bool := by exact (· < ·)) : Array α :=
 swapLeftWhileLT ⟨a.push x, rfl⟩ a.size (by simp) lt |>.toArray

end Array

/-! ### Verification -/

namespace Vector

theorem swapLeftWhileLT_push {n} (a : Vector α n) (x : α) (j : Nat) (h : j < n) :
    swapLeftWhileLT (a.push x) j (by omega) lt = (swapLeftWhileLT a j h lt).push x := by
  induction j generalizing a with
  | zero => simp [swapLeftWhileLT]
  | succ j ih =>
    simp [swapLeftWhileLT]
    split <;> rename_i h
    · rw [Vector.getElem_push_lt (by omega), Vector.getElem_push_lt (by omega)] at h
      rw [if_pos h]
    · rw [Vector.getElem_push_lt (by omega), Vector.getElem_push_lt (by omega)] at h
      rw [← Vector.push_swap, ih, if_neg h]

theorem swapLeftWhileLT_cast {n m} (a : Vector α n) (j : Nat) (h : j < n) (h' : n = m) :
    swapLeftWhileLT (a.cast h') j (by omega) lt = (swapLeftWhileLT a j h lt).cast h' := by
  subst h'
  simp

end Vector

namespace Array

@[simp] theorem size_insertionSort (a : Array α) : (a.insertionSort lt).size = a.size := by
  simp [insertionSort]

private theorem insertionSort_push' (a : Array α) (x : α) :
    (a.push x).insertionSort lt =
      (swapLeftWhileLT ⟨(a.insertionSort lt).push x, rfl⟩ a.size (by simp) lt).toArray := by
  rw [insertionSort, Nat.fold_congr (size_push a x), Nat.fold]
  have : (a.size.fold (fun i h acc => swapLeftWhileLT acc i (by simp; omega) lt) ⟨a.push x, rfl⟩) =
      ((a.size.fold (fun i h acc => swapLeftWhileLT acc i h lt) ⟨a, rfl⟩).push x).cast (by simp) := by
    rw [Vector.eq_cast_iff]
    simp only [Nat.fold_eq_finRange_foldl]
    rw [← List.foldl_hom (fun a => (Vector.push x a)) _ (fun v ⟨i, h⟩ => swapLeftWhileLT v i (by omega) lt)]
    rw [Vector.push_mk]
    rw [← List.foldl_hom (Vector.cast _) _ (fun v ⟨i, h⟩ => swapLeftWhileLT v i (by omega) lt)]
    · simp
    · intro v i
      simp only
      rw [swapLeftWhileLT_cast]
    · simp [swapLeftWhileLT_push]
  rw [this]
  simp only [Nat.lt_add_one, swapLeftWhileLT_cast, Vector.toArray_cast]
  unfold insertionSort
  simp only [Vector.push]
  congr
  all_goals simp

theorem insertionSort_push (a : Array α) (x : α) :
    (a.push x).insertionSort lt = (a.insertionSort lt).orderedInsert x lt := by
  rw [insertionSort_push', orderedInsert]
  simp

end Array
