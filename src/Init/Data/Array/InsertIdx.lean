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

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

open Function

open Nat

namespace Array

universe u

variable {α : Type u}

section InsertIdx

variable {a : α}

@[simp] theorem toList_insertIdx {xs : Array α} {i : Nat} {x : α} (h : i ≤ xs.size) :
    (xs.insertIdx i x h).toList = xs.toList.insertIdx i x := by
  rcases xs with ⟨xs⟩
  simp

@[simp]
theorem insertIdx_zero {xs : Array α} {x : α} : xs.insertIdx 0 x = #[x] ++ xs := by
  rcases xs with ⟨xs⟩
  simp

@[simp] theorem size_insertIdx {xs : Array α} (h : i ≤ xs.size) : (xs.insertIdx i a).size = xs.size + 1 := by
  rcases xs with ⟨xs⟩
  simp [List.length_insertIdx, h]

theorem eraseIdx_insertIdx {i : Nat} {xs : Array α} (h : i ≤ xs.size) :
    (xs.insertIdx i a).eraseIdx i (by simp; omega) = xs := by
  rcases xs with ⟨xs⟩
  simp_all

theorem insertIdx_eraseIdx_of_ge {as : Array α}
    (w₁ : i < as.size) (w₂ : j ≤ (as.eraseIdx i).size) (h : i ≤ j) :
    (as.eraseIdx i).insertIdx j a =
      (as.insertIdx (j + 1) a (by simp at w₂; omega)).eraseIdx i (by simp_all; omega) := by
  cases as
  simpa using List.insertIdx_eraseIdx_of_ge (by simpa) (by simpa)

theorem insertIdx_eraseIdx_of_le {as : Array α}
    (w₁ : i < as.size) (w₂ : j ≤ (as.eraseIdx i).size) (h : j ≤ i) :
    (as.eraseIdx i).insertIdx j a =
      (as.insertIdx j a (by simp at w₂; omega)).eraseIdx (i + 1) (by simp_all) := by
  cases as
  simpa using List.insertIdx_eraseIdx_of_le (by simpa) (by simpa)

theorem insertIdx_comm (a b : α) {i j : Nat} {xs : Array α} (_ : i ≤ j) (_ : j ≤ xs.size) :
    (xs.insertIdx i a).insertIdx (j + 1) b (by simpa) =
      (xs.insertIdx j b).insertIdx i a (by simp; omega) := by
  rcases xs with ⟨xs⟩
  simpa using List.insertIdx_comm a b (by simpa) (by simpa)

theorem mem_insertIdx {xs : Array α} {h : i ≤ xs.size} : a ∈ xs.insertIdx i b h ↔ a = b ∨ a ∈ xs := by
  rcases xs with ⟨xs⟩
  simpa using List.mem_insertIdx (by simpa)

@[simp]
theorem insertIdx_size_self {xs : Array α} {x : α} : xs.insertIdx xs.size x = xs.push x := by
  rcases xs with ⟨xs⟩
  simp

theorem getElem_insertIdx {xs : Array α} {x : α} {i k : Nat} (w : i ≤ xs.size) (h : k < (xs.insertIdx i x).size) :
    (xs.insertIdx i x)[k] =
      if h₁ : k < i then
        xs[k]'(by simp [size_insertIdx] at h; omega)
      else
        if h₂ : k = i then
          x
        else
          xs[k-1]'(by simp [size_insertIdx] at h; omega) := by
  cases xs
  simp [List.getElem_insertIdx, w]

theorem getElem_insertIdx_of_lt {xs : Array α} {x : α} {i k : Nat} (w : i ≤ xs.size) (h : k < i) :
    (xs.insertIdx i x)[k]'(by simp; omega) = xs[k] := by
  simp [getElem_insertIdx, w, h]

theorem getElem_insertIdx_self {xs : Array α} {x : α} {i : Nat} (w : i ≤ xs.size) :
    (xs.insertIdx i x)[i]'(by simp; omega) = x := by
  simp [getElem_insertIdx, w]

theorem getElem_insertIdx_of_gt {xs : Array α} {x : α} {i k : Nat} (w : k ≤ xs.size) (h : k > i) :
    (xs.insertIdx i x)[k]'(by simp; omega) = xs[k - 1]'(by omega) := by
  simp [getElem_insertIdx, w, h]
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem getElem?_insertIdx {xs : Array α} {x : α} {i k : Nat} (h : i ≤ xs.size) :
    (xs.insertIdx i x)[k]? =
      if k < i then
        xs[k]?
      else
        if k = i then
          if k ≤ xs.size then some x else none
        else
          xs[k-1]? := by
  cases xs
  simp [List.getElem?_insertIdx, h]

theorem getElem?_insertIdx_of_lt {xs : Array α} {x : α} {i k : Nat} (w : i ≤ xs.size) (h : k < i) :
    (xs.insertIdx i x)[k]? = xs[k]? := by
  rw [getElem?_insertIdx, if_pos h]

theorem getElem?_insertIdx_self {xs : Array α} {x : α} {i : Nat} (w : i ≤ xs.size) :
    (xs.insertIdx i x)[i]? = some x := by
  rw [getElem?_insertIdx, if_neg (by omega), if_pos rfl, if_pos w]

theorem getElem?_insertIdx_of_ge {xs : Array α} {x : α} {i k : Nat} (w : i < k) (h : k ≤ xs.size) :
    (xs.insertIdx i x)[k]? = xs[k - 1]? := by
  rw [getElem?_insertIdx, if_neg (by omega), if_neg (by omega)]

end InsertIdx

end Array
