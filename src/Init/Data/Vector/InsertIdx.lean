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

open Function

open Nat

namespace Vector

universe u

variable {α : Type u}

section InsertIdx

variable {a : α}

@[simp]
theorem insertIdx_zero (s : Vector α n) (x : α) : s.insertIdx 0 x = (#v[x] ++ s).cast (by omega) := by
  cases s
  simp

theorem eraseIdx_insertIdx (i : Nat) (l : Vector α n) (h : i ≤ n) :
    (l.insertIdx i a).eraseIdx i = l := by
  rcases l with ⟨l, rfl⟩
  simp_all [Array.eraseIdx_insertIdx]

theorem insertIdx_eraseIdx_of_ge {as : Vector α n}
    (w₁ : i < n) (w₂ : j ≤ n - 1) (h : i ≤ j) :
    (as.eraseIdx i).insertIdx j a =
      ((as.insertIdx (j + 1) a).eraseIdx i).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simpa using Array.insertIdx_eraseIdx_of_ge (by simpa) (by simpa) (by simpa)

theorem insertIdx_eraseIdx_of_le {as : Vector α n}
    (w₁ : i < n) (w₂ : j ≤ n - 1) (h : j ≤ i) :
    (as.eraseIdx i).insertIdx j a =
      ((as.insertIdx j a).eraseIdx (i + 1)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simpa using Array.insertIdx_eraseIdx_of_le (by simpa) (by simpa) (by simpa)

theorem insertIdx_comm (a b : α) (i j : Nat) (l : Vector α n) (_ : i ≤ j) (_ : j ≤ n) :
    (l.insertIdx i a).insertIdx (j + 1) b =
      (l.insertIdx j b).insertIdx i a := by
  rcases l with ⟨l, rfl⟩
  simpa using Array.insertIdx_comm a b i j _ (by simpa) (by simpa)

theorem mem_insertIdx {l : Vector α n} {h : i ≤ n} : a ∈ l.insertIdx i b h ↔ a = b ∨ a ∈ l := by
  rcases l with ⟨l, rfl⟩
  simpa using Array.mem_insertIdx

@[simp]
theorem insertIdx_size_self (l : Vector α n) (x : α) : l.insertIdx n x = l.push x := by
  rcases l with ⟨l, rfl⟩
  simp

theorem getElem_insertIdx {as : Vector α n} {x : α} {i k : Nat} (w : i ≤ n) (h : k < n + 1) :
    (as.insertIdx i x)[k] =
      if h₁ : k < i then
        as[k]
      else
        if h₂ : k = i then
          x
        else
          as[k-1] := by
  rcases as with ⟨as, rfl⟩
  simp [Array.getElem_insertIdx, w]

theorem getElem_insertIdx_of_lt {as : Vector α n} {x : α} {i k : Nat} (w : i ≤ n) (h : k < i) :
    (as.insertIdx i x)[k] = as[k] := by
  rcases as with ⟨as, rfl⟩
  simp [Array.getElem_insertIdx, w, h]

theorem getElem_insertIdx_self {as : Vector α n} {x : α} {i : Nat} (w : i ≤ n) :
    (as.insertIdx i x)[i] = x := by
  rcases as with ⟨as, rfl⟩
  simp [Array.getElem_insertIdx, w]

theorem getElem_insertIdx_of_gt {as : Vector α n} {x : α} {i k : Nat} (w : k ≤ n) (h : k > i) :
    (as.insertIdx i x)[k] = as[k - 1] := by
  rcases as with ⟨as, rfl⟩
  simp [Array.getElem_insertIdx, w, h]
  rw [dif_neg (by omega), dif_neg (by omega)]

theorem getElem?_insertIdx {l : Vector α n} {x : α} {i k : Nat} (h : i ≤ n) :
    (l.insertIdx i x)[k]? =
      if k < i then
        l[k]?
      else
        if k = i then
          if k ≤ l.size then some x else none
        else
          l[k-1]? := by
  rcases l with ⟨l, rfl⟩
  simp [Array.getElem?_insertIdx, h]

theorem getElem?_insertIdx_of_lt {l : Vector α n} {x : α} {i k : Nat} (w : i ≤ n) (h : k < i) :
    (l.insertIdx i x)[k]? = l[k]? := by
  rcases l with ⟨l, rfl⟩
  rw [getElem?_insertIdx, if_pos h]

theorem getElem?_insertIdx_self {l : Vector α n} {x : α} {i : Nat} (w : i ≤ n) :
    (l.insertIdx i x)[i]? = some x := by
  rcases l with ⟨l, rfl⟩
  rw [getElem?_insertIdx, if_neg (by omega), if_pos rfl, if_pos w]

theorem getElem?_insertIdx_of_ge {l : Vector α n} {x : α} {i k : Nat} (w : i < k) (h : k ≤ n) :
    (l.insertIdx i x)[k]? = l[k - 1]? := by
  rcases l with ⟨l, rfl⟩
  rw [getElem?_insertIdx, if_neg (by omega), if_neg (by omega)]

end InsertIdx

end Vector
