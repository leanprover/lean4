/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Lemmas
import Init.Data.Array.InsertIdx

/-!
# insertIdx

Proves various lemmas about `Vector.insertIdx`.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

open Function Nat

namespace Vector

universe u

variable {α : Type u}

section InsertIdx

variable {a : α}

@[simp]
theorem insertIdx_zero (xs : Vector α n) (x : α) : xs.insertIdx 0 x = (#v[x] ++ xs).cast (by omega) := by
  cases xs
  simp

theorem eraseIdx_insertIdx (i : Nat) (xs : Vector α n) (h : i ≤ n) :
    (xs.insertIdx i a).eraseIdx i = xs := by
  rcases xs with ⟨xs, rfl⟩
  simp_all [Array.eraseIdx_insertIdx]

theorem insertIdx_eraseIdx_of_ge {xs : Vector α n}
    (w₁ : i < n) (w₂ : j ≤ n - 1) (h : i ≤ j) :
    (xs.eraseIdx i).insertIdx j a =
      ((xs.insertIdx (j + 1) a).eraseIdx i).cast (by omega) := by
  rcases xs with ⟨as, rfl⟩
  simpa using Array.insertIdx_eraseIdx_of_ge (by simpa) (by simpa) (by simpa)

theorem insertIdx_eraseIdx_of_le {xs : Vector α n}
    (w₁ : i < n) (w₂ : j ≤ n - 1) (h : j ≤ i) :
    (xs.eraseIdx i).insertIdx j a =
      ((xs.insertIdx j a).eraseIdx (i + 1)).cast (by omega) := by
  rcases xs with ⟨as, rfl⟩
  simpa using Array.insertIdx_eraseIdx_of_le (by simpa) (by simpa) (by simpa)

theorem insertIdx_comm (a b : α) (i j : Nat) (xs : Vector α n) (_ : i ≤ j) (_ : j ≤ n) :
    (xs.insertIdx i a).insertIdx (j + 1) b =
      (xs.insertIdx j b).insertIdx i a := by
  rcases xs with ⟨as, rfl⟩
  simpa using Array.insertIdx_comm a b i j _ (by simpa) (by simpa)

theorem mem_insertIdx {xs : Vector α n} {h : i ≤ n} : a ∈ xs.insertIdx i b h ↔ a = b ∨ a ∈ xs := by
  rcases xs with ⟨as, rfl⟩
  simpa using Array.mem_insertIdx

set_option linter.indexVariables false in
@[simp]
theorem insertIdx_size_self (xs : Vector α n) (x : α) : xs.insertIdx n x = xs.push x := by
  rcases xs with ⟨as, rfl⟩
  simp

theorem getElem_insertIdx {xs : Vector α n} {x : α} {i k : Nat} (w : i ≤ n) (h : k < n + 1) :
    (xs.insertIdx i x)[k] =
      if h₁ : k < i then
        xs[k]
      else
        if h₂ : k = i then
          x
        else
          xs[k-1] := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem_insertIdx, w]

theorem getElem_insertIdx_of_lt {xs : Vector α n} {x : α} {i k : Nat} (w : i ≤ n) (h : k < i) :
    (xs.insertIdx i x)[k] = xs[k] := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem_insertIdx, w, h]

theorem getElem_insertIdx_self {xs : Vector α n} {x : α} {i : Nat} (w : i ≤ n) :
    (xs.insertIdx i x)[i] = x := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem_insertIdx, w]

theorem getElem_insertIdx_of_gt {xs : Vector α n} {x : α} {i k : Nat} (w : k ≤ n) (h : k > i) :
    (xs.insertIdx i x)[k] = xs[k - 1] := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem_insertIdx, w, h]
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem getElem?_insertIdx {xs : Vector α n} {x : α} {i k : Nat} (h : i ≤ n) :
    (xs.insertIdx i x)[k]? =
      if k < i then
        xs[k]?
      else
        if k = i then
          if k ≤ xs.size then some x else none
        else
          xs[k-1]? := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem?_insertIdx, h]

theorem getElem?_insertIdx_of_lt {xs : Vector α n} {x : α} {i k : Nat} (w : i ≤ n) (h : k < i) :
    (xs.insertIdx i x)[k]? = xs[k]? := by
  rcases xs with ⟨xs, rfl⟩
  rw [getElem?_insertIdx, if_pos h]

theorem getElem?_insertIdx_self {xs : Vector α n} {x : α} {i : Nat} (w : i ≤ n) :
    (xs.insertIdx i x)[i]? = some x := by
  rcases xs with ⟨xs, rfl⟩
  rw [getElem?_insertIdx, if_neg (by omega), if_pos rfl, if_pos w]

theorem getElem?_insertIdx_of_ge {xs : Vector α n} {x : α} {i k : Nat} (w : i < k) (h : k ≤ n) :
    (xs.insertIdx i x)[k]? = xs[k - 1]? := by
  rcases xs with ⟨xs, rfl⟩
  rw [getElem?_insertIdx, if_neg (by omega), if_neg (by omega)]

end InsertIdx

end Vector
