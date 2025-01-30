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

namespace Vector

open Nat

/-! ### eraseIdx -/

theorem eraseIdx_eq_take_drop_succ (l : Vector α n) (i : Nat) (h) :
    l.eraseIdx i = (l.take i ++ l.drop (i + 1)).cast (by omega) := by
  rcases l with ⟨l, rfl⟩
  simp [Array.eraseIdx_eq_take_drop_succ, *]

theorem getElem?_eraseIdx (l : Vector α n) (i : Nat) (h : i < n) (j : Nat) :
    (l.eraseIdx i)[j]? = if j < i then l[j]? else l[j + 1]? := by
  rcases l with ⟨l, rfl⟩
  simp [Array.getElem?_eraseIdx]

theorem getElem?_eraseIdx_of_lt (l : Vector α n) (i : Nat) (h : i < n) (j : Nat) (h' : j < i) :
    (l.eraseIdx i)[j]? = l[j]? := by
  rw [getElem?_eraseIdx]
  simp [h']

theorem getElem?_eraseIdx_of_ge (l : Vector α n) (i : Nat) (h : i < n) (j : Nat) (h' : i ≤ j) :
    (l.eraseIdx i)[j]? = l[j + 1]? := by
  rw [getElem?_eraseIdx]
  simp only [dite_eq_ite, ite_eq_right_iff]
  intro h'
  omega

theorem getElem_eraseIdx (l : Vector α n) (i : Nat) (h : i < n) (j : Nat) (h' : j < n - 1) :
    (l.eraseIdx i)[j] = if h'' : j < i then l[j] else l[j + 1] := by
  apply Option.some.inj
  rw [← getElem?_eq_getElem, getElem?_eraseIdx]
  split <;> simp

theorem mem_of_mem_eraseIdx {l : Vector α n} {i : Nat} {h} {a : α} (h : a ∈ l.eraseIdx i) : a ∈ l := by
  rcases l with ⟨l, rfl⟩
  simpa using Array.mem_of_mem_eraseIdx (by simpa using h)

theorem eraseIdx_append_of_lt_size {l : Vector α n} {k : Nat} (hk : k < n) (l' : Vector α n) (h) :
    eraseIdx (l ++ l') k = (eraseIdx l k ++ l').cast (by omega) := by
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp [Array.eraseIdx_append_of_lt_size, *]

theorem eraseIdx_append_of_length_le {l : Vector α n} {k : Nat} (hk : n ≤ k) (l' : Vector α n) (h) :
    eraseIdx (l ++ l') k = (l ++ eraseIdx l' (k - n)).cast (by omega) := by
  rcases l with ⟨l⟩
  rcases l' with ⟨l'⟩
  simp [Array.eraseIdx_append_of_length_le, *]

theorem eraseIdx_cast {l : Vector α n} {k : Nat} (h : k < m) :
    eraseIdx (l.cast w) k h = (eraseIdx l k).cast (by omega) := by
  rcases l with ⟨l, rfl⟩
  simp

theorem eraseIdx_mkVector {n : Nat} {a : α} {k : Nat} {h} :
    (mkVector n a).eraseIdx k = mkVector (n - 1) a := by
  rw [mkVector_eq_mk_mkArray, eraseIdx_mk]
  simp [Array.eraseIdx_mkArray, *]

theorem mem_eraseIdx_iff_getElem {x : α} {l : Vector α n} {k} {h} : x ∈ eraseIdx l k h ↔ ∃ i w, i ≠ k ∧ l[i]'w = x := by
  rcases l with ⟨l, rfl⟩
  simp [Array.mem_eraseIdx_iff_getElem, *]

theorem mem_eraseIdx_iff_getElem? {x : α} {l : Vector α n} {k} {h} : x ∈ eraseIdx l k h ↔ ∃ i ≠ k, l[i]? = some x := by
  rcases l with ⟨l, rfl⟩
  simp [Array.mem_eraseIdx_iff_getElem?, *]

theorem getElem_eraseIdx_of_lt (l : Vector α n) (i : Nat) (w : i < n) (j : Nat) (h : j < n - 1) (h' : j < i) :
    (l.eraseIdx i)[j] = l[j] := by
  rcases l with ⟨l, rfl⟩
  simp [Array.getElem_eraseIdx_of_lt, *]

theorem getElem_eraseIdx_of_ge (l : Vector α n) (i : Nat) (w : i < n) (j : Nat) (h : j < n - 1) (h' : i ≤ j) :
    (l.eraseIdx i)[j] = l[j + 1] := by
  rcases l with ⟨l, rfl⟩
  simp [Array.getElem_eraseIdx_of_ge, *]

theorem eraseIdx_set_eq {l : Vector α n} {i : Nat} {a : α} {h : i < n} :
    (l.set i a).eraseIdx i = l.eraseIdx i := by
  rcases l with ⟨l, rfl⟩
  simp [Array.eraseIdx_set_eq, *]

theorem eraseIdx_set_lt {l : Vector α n} {i : Nat} {w : i < n} {j : Nat} {a : α} (h : j < i) :
    (l.set i a).eraseIdx j = (l.eraseIdx j).set (i - 1) a := by
  rcases l with ⟨l, rfl⟩
  simp [Array.eraseIdx_set_lt, *]

theorem eraseIdx_set_gt {l : Vector α n} {i : Nat} {j : Nat} {a : α} (h : i < j) {w : j < n} :
    (l.set i a).eraseIdx j = (l.eraseIdx j).set i a := by
  rcases l with ⟨l, rfl⟩
  simp [Array.eraseIdx_set_gt, *]

@[simp] theorem set_getElem_succ_eraseIdx_succ
    {l : Vector α n} {i : Nat} (h : i + 1 < n) :
    (l.eraseIdx (i + 1)).set i l[i + 1] = l.eraseIdx i := by
  rcases l with ⟨l, rfl⟩
  simp [List.set_getElem_succ_eraseIdx_succ, *]

end Vector
