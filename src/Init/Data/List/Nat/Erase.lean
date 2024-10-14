/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Erase

namespace List

theorem getElem?_eraseIdx (l : List α) (i : Nat) (j : Nat) :
    (l.eraseIdx i)[j]? = if j < i then l[j]? else l[j + 1]? := by
  rw [eraseIdx_eq_take_drop_succ, getElem?_append]
  split <;> rename_i h
  · rw [getElem?_take]
    split
    · rfl
    · simp_all
      omega
  · rw [getElem?_drop]
    split <;> rename_i h'
    · simp only [length_take, Nat.min_def, Nat.not_lt] at h
      split at h
      · omega
      · simp_all [getElem?_eq_none]
        omega
    · simp only [length_take]
      simp only [length_take, Nat.min_def, Nat.not_lt] at h
      split at h
      · congr 1
        omega
      · rw [getElem?_eq_none, getElem?_eq_none] <;> omega

theorem getElem?_eraseIdx_of_lt (l : List α) (i : Nat) (j : Nat) (h : j < i) :
    (l.eraseIdx i)[j]? = l[j]? := by
  rw [getElem?_eraseIdx]
  simp [h]

theorem getElem?_eraseIdx_of_ge (l : List α) (i : Nat) (j : Nat) (h : i ≤ j) :
    (l.eraseIdx i)[j]? = l[j + 1]? := by
  rw [getElem?_eraseIdx]
  simp only [dite_eq_ite, ite_eq_right_iff]
  intro h'
  omega

theorem getElem_eraseIdx (l : List α) (i : Nat) (j : Nat) (h : j < (l.eraseIdx i).length) :
    (l.eraseIdx i)[j] = if h' : j < i then
        l[j]'(by have := length_eraseIdx_le l i; omega)
      else
        l[j + 1]'(by rw [length_eraseIdx] at h; split at h <;> omega) := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, getElem?_eraseIdx]
  split <;> simp

theorem getElem_eraseIdx_of_lt (l : List α) (i : Nat) (j : Nat) (h : j < (l.eraseIdx i).length) (h' : j < i) :
    (l.eraseIdx i)[j] = l[j]'(by have := length_eraseIdx_le l i; omega) := by
  rw [getElem_eraseIdx]
  simp only [dite_eq_left_iff, Nat.not_lt]
  intro h'
  omega

theorem getElem_eraseIdx_of_ge (l : List α) (i : Nat) (j : Nat) (h : j < (l.eraseIdx i).length) (h' : i ≤ j) :
    (l.eraseIdx i)[j] = l[j + 1]'(by rw [length_eraseIdx] at h; split at h <;> omega) := by
  rw [getElem_eraseIdx, dif_neg]
  omega
