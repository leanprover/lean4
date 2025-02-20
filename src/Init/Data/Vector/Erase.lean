/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Lemmas
import Init.Data.Array.Erase

/-!
# Lemmas about `Vector.eraseIdx`.
-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

open Nat

/-! ### eraseIdx -/

theorem eraseIdx_eq_take_drop_succ (xs : Vector α n) (i : Nat) (h) :
    xs.eraseIdx i = (xs.take i ++ xs.drop (i + 1)).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.eraseIdx_eq_take_drop_succ, *]

theorem getElem?_eraseIdx (xs : Vector α n) (i : Nat) (h : i < n) (j : Nat) :
    (xs.eraseIdx i)[j]? = if j < i then xs[j]? else xs[j + 1]? := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.getElem?_eraseIdx]

theorem getElem?_eraseIdx_of_lt (xs : Vector α n) (i : Nat) (h : i < n) (j : Nat) (h' : j < i) :
    (xs.eraseIdx i)[j]? = xs[j]? := by
  rw [getElem?_eraseIdx]
  simp [h']

theorem getElem?_eraseIdx_of_ge (xs : Vector α n) (i : Nat) (h : i < n) (j : Nat) (h' : i ≤ j) :
    (xs.eraseIdx i)[j]? = xs[j + 1]? := by
  rw [getElem?_eraseIdx]
  simp only [dite_eq_ite, ite_eq_right_iff]
  intro h'
  omega

theorem getElem_eraseIdx (xs : Vector α n) (i : Nat) (h : i < n) (j : Nat) (h' : j < n - 1) :
    (xs.eraseIdx i)[j] = if h'' : j < i then xs[j] else xs[j + 1] := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, getElem?_eraseIdx]
  split <;> simp

theorem mem_of_mem_eraseIdx {xs : Vector α n} {i : Nat} {h} {a : α} (h : a ∈ xs.eraseIdx i) : a ∈ xs := by
  rcases xs with ⟨xs, rfl⟩
  simpa using Array.mem_of_mem_eraseIdx (by simpa using h)

theorem eraseIdx_append_of_lt_size {xs : Vector α n} {k : Nat} (hk : k < n) (xs' : Vector α n) (h) :
    eraseIdx (xs ++ xs') k = (eraseIdx xs k ++ xs').cast (by omega) := by
  rcases xs with ⟨xs⟩
  rcases xs' with ⟨xs'⟩
  simp [Array.eraseIdx_append_of_lt_size, *]

theorem eraseIdx_append_of_length_le {xs : Vector α n} {k : Nat} (hk : n ≤ k) (xs' : Vector α n) (h) :
    eraseIdx (xs ++ xs') k = (xs ++ eraseIdx xs' (k - n)).cast (by omega) := by
  rcases xs with ⟨xs⟩
  rcases xs' with ⟨xs'⟩
  simp [Array.eraseIdx_append_of_length_le, *]

theorem eraseIdx_cast {xs : Vector α n} {k : Nat} (h : k < m) :
    eraseIdx (xs.cast w) k h = (eraseIdx xs k).cast (by omega) := by
  rcases xs with ⟨xs⟩
  simp

theorem eraseIdx_mkVector {n : Nat} {a : α} {k : Nat} {h} :
    (mkVector n a).eraseIdx k = mkVector (n - 1) a := by
  rw [mkVector_eq_mk_mkArray, eraseIdx_mk]
  simp [Array.eraseIdx_mkArray, *]

theorem mem_eraseIdx_iff_getElem {x : α} {xs : Vector α n} {k} {h} : x ∈ xs.eraseIdx k h ↔ ∃ i w, i ≠ k ∧ xs[i]'w = x := by
  rcases xs with ⟨xs⟩
  simp [Array.mem_eraseIdx_iff_getElem, *]

theorem mem_eraseIdx_iff_getElem? {x : α} {xs : Vector α n} {k} {h} : x ∈ xs.eraseIdx k h ↔ ∃ i ≠ k, xs[i]? = some x := by
  rcases xs with ⟨xs⟩
  simp [Array.mem_eraseIdx_iff_getElem?, *]

theorem getElem_eraseIdx_of_lt (xs : Vector α n) (i : Nat) (w : i < n) (j : Nat) (h : j < n - 1) (h' : j < i) :
    (xs.eraseIdx i)[j] = xs[j] := by
  rcases xs with ⟨xs⟩
  simp [Array.getElem_eraseIdx_of_lt, *]

theorem getElem_eraseIdx_of_ge (xs : Vector α n) (i : Nat) (w : i < n) (j : Nat) (h : j < n - 1) (h' : i ≤ j) :
    (xs.eraseIdx i)[j] = xs[j + 1] := by
  rcases xs with ⟨xs⟩
  simp [Array.getElem_eraseIdx_of_ge, *]

theorem eraseIdx_set_eq {xs : Vector α n} {i : Nat} {a : α} {h : i < n} :
    (xs.set i a).eraseIdx i = xs.eraseIdx i := by
  rcases xs with ⟨xs⟩
  simp [Array.eraseIdx_set_eq, *]

theorem eraseIdx_set_lt {xs : Vector α n} {i : Nat} {w : i < n} {j : Nat} {a : α} (h : j < i) :
    (xs.set i a).eraseIdx j = (xs.eraseIdx j).set (i - 1) a := by
  rcases xs with ⟨xs⟩
  simp [Array.eraseIdx_set_lt, *]

theorem eraseIdx_set_gt {xs : Vector α n} {i : Nat} {j : Nat} {a : α} (h : i < j) {w : j < n} :
    (xs.set i a).eraseIdx j = (xs.eraseIdx j).set i a := by
  rcases xs with ⟨xs⟩
  simp [Array.eraseIdx_set_gt, *]

@[simp] theorem set_getElem_succ_eraseIdx_succ
    {xs : Vector α n} {i : Nat} (h : i + 1 < n) :
    (xs.eraseIdx (i + 1)).set i xs[i + 1] = xs.eraseIdx i := by
  rcases xs with ⟨xs⟩
  simp [Array.set_getElem_succ_eraseIdx_succ, *]

end Vector
