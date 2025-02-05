/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.List.Nat.InsertIdx

/-!
# insertIdx

Proves various lemmas about `Array.insertIdx`.
-/

open Function

open Nat

namespace Array

universe u

variable {α : Type u}

section InsertIdx

variable {a : α}

@[simp] theorem toList_insertIdx (a : Array α) (i x) (h) :
    (a.insertIdx i x h).toList = a.toList.insertIdx i x := by
  rcases a with ⟨a⟩
  simp

@[simp]
theorem insertIdx_zero (s : Array α) (x : α) : s.insertIdx 0 x = #[x] ++ s := by
  cases s
  simp

@[simp] theorem size_insertIdx {as : Array α} (h : n ≤ as.size) : (as.insertIdx n a).size = as.size + 1 := by
  cases as
  simp [List.length_insertIdx, h]

theorem eraseIdx_insertIdx (i : Nat) (l : Array α) (h : i ≤ l.size) :
    (l.insertIdx i a).eraseIdx i (by simp; omega) = l := by
  cases l
  simp_all

theorem insertIdx_eraseIdx_of_ge {as : Array α}
    (w₁ : i < as.size) (w₂ : j ≤ (as.eraseIdx i).size) (h : i ≤ j) :
    (as.eraseIdx i).insertIdx j a =
      (as.insertIdx (j + 1) a (by simp at w₂; omega)).eraseIdx i (by simp_all; omega) := by
  cases as
  simpa using List.insertIdx_eraseIdx_of_ge _ _ _ (by simpa) (by simpa)

theorem insertIdx_eraseIdx_of_le {as : Array α}
    (w₁ : i < as.size) (w₂ : j ≤ (as.eraseIdx i).size) (h : j ≤ i) :
    (as.eraseIdx i).insertIdx j a =
      (as.insertIdx j a (by simp at w₂; omega)).eraseIdx (i + 1) (by simp_all) := by
  cases as
  simpa using List.insertIdx_eraseIdx_of_le _ _ _ (by simpa) (by simpa)

theorem insertIdx_comm (a b : α) (i j : Nat) (l : Array α) (_ : i ≤ j) (_ : j ≤ l.size) :
    (l.insertIdx i a).insertIdx (j + 1) b (by simpa) =
      (l.insertIdx j b).insertIdx i a (by simp; omega) := by
  cases l
  simpa using List.insertIdx_comm a b i j _ (by simpa) (by simpa)

theorem mem_insertIdx {l : Array α} {h : i ≤ l.size} : a ∈ l.insertIdx i b h ↔ a = b ∨ a ∈ l := by
  cases l
  simpa using List.mem_insertIdx (by simpa)

@[simp]
theorem insertIdx_size_self (l : Array α) (x : α) : l.insertIdx l.size x = l.push x := by
  cases l
  simp

theorem getElem_insertIdx {as : Array α} {x : α} {i k : Nat} (w : i ≤ as.size) (h : k < (as.insertIdx i x).size) :
    (as.insertIdx i x)[k] =
      if h₁ : k < i then
        as[k]'(by simp [size_insertIdx] at h; omega)
      else
        if h₂ : k = i then
          x
        else
          as[k-1]'(by simp [size_insertIdx] at h; omega) := by
  cases as
  simp [List.getElem_insertIdx, w]

theorem getElem_insertIdx_of_lt {as : Array α} {x : α} {i k : Nat} (w : i ≤ as.size) (h : k < i) :
    (as.insertIdx i x)[k]'(by simp; omega) = as[k] := by
  simp [getElem_insertIdx, w, h]

theorem getElem_insertIdx_self {as : Array α} {x : α} {i : Nat} (w : i ≤ as.size) :
    (as.insertIdx i x)[i]'(by simp; omega) = x := by
  simp [getElem_insertIdx, w]

theorem getElem_insertIdx_of_gt {as : Array α} {x : α} {i k : Nat} (w : k ≤ as.size) (h : k > i) :
    (as.insertIdx i x)[k]'(by simp; omega) = as[k - 1]'(by omega) := by
  simp [getElem_insertIdx, w, h]
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem getElem?_insertIdx {l : Array α} {x : α} {i k : Nat} (h : i ≤ l.size) :
    (l.insertIdx i x)[k]? =
      if k < i then
        l[k]?
      else
        if k = i then
          if k ≤ l.size then some x else none
        else
          l[k-1]? := by
  cases l
  simp [List.getElem?_insertIdx, h]

theorem getElem?_insertIdx_of_lt {l : Array α} {x : α} {i k : Nat} (w : i ≤ l.size) (h : k < i) :
    (l.insertIdx i x)[k]? = l[k]? := by
  rw [getElem?_insertIdx, if_pos h]

theorem getElem?_insertIdx_self {l : Array α} {x : α} {i : Nat} (w : i ≤ l.size) :
    (l.insertIdx i x)[i]? = some x := by
  rw [getElem?_insertIdx, if_neg (by omega), if_pos rfl, if_pos w]

theorem getElem?_insertIdx_of_ge {l : Array α} {x : α} {i k : Nat} (w : i < k) (h : k ≤ l.size) :
    (l.insertIdx i x)[k]? = l[k - 1]? := by
  rw [getElem?_insertIdx, if_neg (by omega), if_neg (by omega)]

end InsertIdx

end Array
