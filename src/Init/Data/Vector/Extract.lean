/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Lemmas
import Init.Data.Array.Extract

/-!
# Lemmas about `Vector.extract`
-/

open Nat

namespace Vector

/-! ### extract -/

@[simp] theorem extract_of_size_lt {as : Vector α n} {i j : Nat} (h : n < j) :
    as.extract i j = (as.extract i n).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp [h]

@[simp]
theorem extract_push {as : Vector α n} {b : α} {start stop : Nat} (h : stop ≤ n) :
    (as.push b).extract start stop = (as.extract start stop).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp [h]

@[simp]
theorem extract_eq_pop {as : Vector α n} {stop : Nat} (h : stop = n - 1) :
    as.extract 0 stop = as.pop.cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp [h]

@[simp]
theorem extract_append_extract {as : Vector α n} {i j k : Nat} :
    as.extract i j ++ as.extract j k =
      (as.extract (min i j) (max j k)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp

@[simp]
theorem push_extract_getElem {as : Vector α n} {i j : Nat} (h : j < n) :
    (as.extract i j).push as[j] = (as.extract (min i j) (j + 1)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp [h]

theorem extract_succ_right {as : Vector α n} {i j : Nat} (w : i < j + 1) (h : j < n) :
    as.extract i (j + 1) = ((as.extract i j).push as[j]).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp [Array.extract_succ_right, w, h]

theorem extract_sub_one {as : Vector α n} {i j : Nat} (h : j < n) :
    as.extract i (j - 1) = (as.extract i j).pop.cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp [Array.extract_sub_one, h]

@[simp]
theorem getElem?_extract_of_lt {as : Vector α n} {i j k : Nat} (h : k < min j n - i) :
    (as.extract i j)[k]? = some (as[i + k]'(by omega)) := by
  simp [getElem?_extract, h]

theorem getElem?_extract_of_succ {as : Vector α n} {j : Nat} :
    (as.extract 0 (j + 1))[j]? = as[j]? := by
  simp only [Nat.sub_zero]
  erw [getElem?_extract] -- Why does this not fire by `simp` or `rw`?
  by_cases h : j < n
  · rw [if_pos (by omega)]
    simp
  · rw [if_neg (by omega)]
    simp_all

@[simp] theorem extract_extract {as : Vector α n} {i j k l : Nat} :
    (as.extract i j).extract k l = (as.extract (i + k) (min (i + l) j)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp

theorem extract_set {as : Vector α n} {i j k : Nat} (h : k < n) {a : α} :
    (as.set k a).extract i j =
      if _ : k < i then
        as.extract i j
      else if _ : k < min j as.size then
        (as.extract i j).set (k - i) a (by omega)
      else as.extract i j := by
  rcases as with ⟨as, rfl⟩
  simp only [set_mk, extract_mk, Array.extract_set]
  split
  · simp
  · split <;> simp

theorem set_extract {as : Vector α n} {i j k : Nat} (h : k < min j n - i) {a : α} :
    (as.extract i j).set k a = (as.set (i + k) a).extract i j := by
  rcases as with ⟨as, rfl⟩
  simp [Array.set_extract]

@[simp]
theorem extract_append {as : Vector α n} {bs : Vector α m} {i j : Nat} :
    (as ++ bs).extract i j =
      (as.extract i j ++ bs.extract (i - n) (j - n)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  simp

theorem extract_append_left {as : Vector α n} {bs : Vector α m} :
    (as ++ bs).extract 0 n = (as.extract 0 n).cast (by omega) := by
  ext i h
  simp only [Nat.sub_zero, extract_append, extract_size, getElem_cast, getElem_append, Nat.min_self,
    getElem_extract, Nat.zero_sub, Nat.zero_add, cast_cast]
  split
  · rfl
  · omega

@[simp] theorem extract_append_right {as : Vector α n} {bs : Vector α m} :
    (as ++ bs).extract n (n + i) = (bs.extract 0 i).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  rcases bs with ⟨bs, rfl⟩
  simp only [mk_append_mk, extract_mk, Array.extract_append, Array.extract_size_left, Nat.sub_self,
    Array.empty_append, Nat.sub_zero, cast_mk, eq_mk]
  congr 1
  omega

@[simp] theorem map_extract {as : Vector α n} {i j : Nat} :
    (as.extract i j).map f = (as.map f).extract i j := by
  ext k h
  simp

@[simp] theorem extract_mkVector {a : α} {n i j : Nat} :
    (mkVector n a).extract i j = mkVector (min j n - i) a := by
  ext i h
  simp

theorem extract_add_left {as : Vector α n} {i j k : Nat} :
    as.extract (i + j) k = ((as.extract i k).extract j (k - i)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp only [extract_mk, Array.extract_extract, cast_mk, eq_mk]
  rw [Array.extract_add_left]
  simp

theorem mem_extract_iff_getElem {as : Vector α n} {a : α} {i j : Nat} :
    a ∈ as.extract i j ↔ ∃ (k : Nat) (hm : k < min j n - i), as[i + k] = a := by
  rcases as with ⟨as⟩
  simp [Array.mem_extract_iff_getElem]
  constructor <;>
  · rintro ⟨k, h, rfl⟩
    exact ⟨k, by omega, rfl⟩

theorem set_eq_push_extract_append_extract {as : Vector α n} {i : Nat} (h : i < n) {a : α} :
    as.set i a = ((as.extract 0 i).push a ++ (as.extract (i + 1) n)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp [Array.set_eq_push_extract_append_extract, h]

theorem extract_reverse {as : Vector α n} {i j : Nat} :
    as.reverse.extract i j = (as.extract (n - j) (n - i)).reverse.cast (by omega) := by
  ext i h
  simp only [getElem_extract, getElem_reverse, getElem_cast]
  congr 1
  omega

theorem reverse_extract {as : Vector α n} {i j : Nat} :
    (as.extract i j).reverse = (as.reverse.extract (n - j) (n - i)).cast (by omega) := by
  rcases as with ⟨as, rfl⟩
  simp [Array.reverse_extract]

end Vector
