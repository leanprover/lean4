/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.Vector.Lemmas
import Init.Data.Array.Extract

set_option maxHeartbeats 20000000

/-!
# Lemmas about `Vector.extract`
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

open Nat

namespace Vector

/-! ### extract -/

set_option linter.indexVariables false
@[simp] theorem extract_of_size_lt {xs : Vector α n} {i j : Nat} (h : n < j) :
    xs.extract i j = (xs.extract i n).cast (by omega) := by
  rcases xs with ⟨as, rfl⟩
  simp [h]

@[simp]
theorem extract_push {xs : Vector α n} {b : α} {start stop : Nat} (h : stop ≤ n) :
    (xs.push b).extract start stop = (xs.extract start stop).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp [h]

@[simp]
theorem extract_eq_pop {xs : Vector α n} {stop : Nat} (h : stop = n - 1) :
    xs.extract 0 stop = xs.pop.cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp [h]

@[simp]
theorem extract_append_extract {xs : Vector α n} {i j k : Nat} :
    xs.extract i j ++ xs.extract j k =
      (xs.extract (min i j) (max j k)).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp]
theorem push_extract_getElem {xs : Vector α n} {i j : Nat} (h : j < n) :
    (xs.extract i j).push xs[j] = (xs.extract (min i j) (j + 1)).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp [h]

theorem extract_succ_right {xs : Vector α n} {i j : Nat} (w : i < j + 1) (h : j < n) :
    xs.extract i (j + 1) = ((xs.extract i j).push xs[j]).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.extract_succ_right, w, h]

theorem extract_sub_one {xs : Vector α n} {i j : Nat} (h : j < n) :
    xs.extract i (j - 1) = (xs.extract i j).pop.cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.extract_sub_one, h]

@[simp]
theorem getElem?_extract_of_lt {xs : Vector α n} {i j k : Nat} (h : k < min j n - i) :
    (xs.extract i j)[k]? = some (xs[i + k]'(by omega)) := by
  rcases xs with ⟨xs, rfl⟩
  simp [getElem?_extract, h]

theorem getElem?_extract_of_succ {xs : Vector α n} {j : Nat} :
    (xs.extract 0 (j + 1))[j]? = xs[j]? := by
  simp only [Nat.sub_zero]
  erw [getElem?_extract] -- Why does this not fire by `simp` or `rw`?
  by_cases h : j < n
  · rw [if_pos (by omega)]
    simp
  · rw [if_neg (by omega)]
    simp_all

@[simp] theorem extract_extract {xs : Vector α n} {i j k l : Nat} :
    (xs.extract i j).extract k l = (xs.extract (i + k) (min (i + l) j)).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp

theorem extract_set {xs : Vector α n} {i j k : Nat} (h : k < n) {a : α} :
    (xs.set k a).extract i j =
      if _ : k < i then
        xs.extract i j
      else if _ : k < min j n then
        (xs.extract i j).set (k - i) a (by omega)
      else xs.extract i j := by
  rcases xs with ⟨xs, rfl⟩
  simp only [set_mk, extract_mk, Array.extract_set]
  split
  · simp
  · split <;> simp

theorem set_extract {xs : Vector α n} {i j k : Nat} (h : k < min j n - i) {a : α} :
    (xs.extract i j).set k a = (xs.set (i + k) a).extract i j := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.set_extract]

@[simp]
theorem extract_append {xs : Vector α n} {ys : Vector α m} {i j : Nat} :
    (xs ++ ys).extract i j =
      (xs.extract i j ++ ys.extract (i - n) (j - n)).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp

theorem extract_append_left {xs : Vector α n} {ys : Vector α m} :
    (xs ++ ys).extract 0 n = (xs.extract 0 n).cast (by omega) := by
  ext i h
  simp only [Nat.sub_zero, extract_append, extract_size, getElem_cast, getElem_append, Nat.min_self,
    getElem_extract, Nat.zero_sub, Nat.zero_add, cast_cast]
  split
  · rfl
  · omega

@[simp] theorem extract_append_right {xs : Vector α n} {ys : Vector α m} :
    (xs ++ ys).extract n (n + i) = (ys.extract 0 i).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp only [mk_append_mk, extract_mk, Array.extract_append, Array.extract_size_left, Nat.sub_self,
    Array.empty_append, Nat.sub_zero, cast_mk, eq_mk]
  congr 1
  omega

@[simp] theorem map_extract {xs : Vector α n} {i j : Nat} :
    (xs.extract i j).map f = (xs.map f).extract i j := by
  rcases xs with ⟨xs, rfl⟩
  simp

@[simp] theorem extract_replicate {a : α} {n i j : Nat} :
    (replicate n a).extract i j = replicate (min j n - i) a := by
  ext i h
  simp

@[deprecated extract_mkVector (since := "2025-03-18")]
abbrev extract_mkVector := @extract_replicate

theorem extract_add_left {xs : Vector α n} {i j k : Nat} :
    xs.extract (i + j) k = ((xs.extract i k).extract j (k - i)).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp only [extract_mk, Array.extract_extract, cast_mk, eq_mk]
  rw [Array.extract_add_left]
  simp

theorem mem_extract_iff_getElem {xs : Vector α n} {a : α} {i j : Nat} :
    a ∈ xs.extract i j ↔ ∃ (k : Nat) (hm : k < min j n - i), xs[i + k] = a := by
  rcases xs with ⟨xs⟩
  simp [Array.mem_extract_iff_getElem]
  constructor <;>
  · rintro ⟨k, h, rfl⟩
    exact ⟨k, by omega, rfl⟩

theorem set_eq_push_extract_append_extract {xs : Vector α n} {i : Nat} (h : i < n) {a : α} :
    xs.set i a = ((xs.extract 0 i).push a ++ (xs.extract (i + 1) n)).cast (by omega) := by
  rcases xs with ⟨as, rfl⟩
  simp [Array.set_eq_push_extract_append_extract, h]

theorem extract_reverse {xs : Vector α n} {i j : Nat} :
    xs.reverse.extract i j = (xs.extract (n - j) (n - i)).reverse.cast (by omega) := by
  ext i h
  simp only [getElem_extract, getElem_reverse, getElem_cast]
  congr 1
  omega

theorem reverse_extract {xs : Vector α n} {i j : Nat} :
    (xs.extract i j).reverse = (xs.reverse.extract (n - j) (n - i)).cast (by omega) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.reverse_extract]

end Vector
