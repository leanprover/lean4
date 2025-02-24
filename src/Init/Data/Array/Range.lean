/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.Array.OfFn
import Init.Data.Array.MapIdx
import Init.Data.Array.Zip
import Init.Data.List.Nat.Range

/-!
# Lemmas about `Array.range'`, `Array.range`, and `Array.zipIdx`

-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

open Nat

/-! ## Ranges and enumeration -/

/-! ### range' -/

theorem range'_succ (s n step) : range' s (n + 1) step = #[s] ++ range' (s + step) n step := by
  rw [← toList_inj]
  simp [List.range'_succ]

@[simp] theorem range'_eq_empty_iff : range' s n step = #[] ↔ n = 0 := by
  rw [← size_eq_zero_iff, size_range']

theorem range'_ne_empty_iff (s : Nat) {n step : Nat} : range' s n step ≠ #[] ↔ n ≠ 0 := by
  cases n <;> simp

@[simp] theorem range'_zero : range' s 0 step = #[] := by
  simp

@[simp] theorem range'_one {s step : Nat} : range' s 1 step = #[s] := rfl

@[simp] theorem range'_inj : range' s n = range' s' n' ↔ n = n' ∧ (n = 0 ∨ s = s') := by
  rw [← toList_inj]
  simp [List.range'_inj]

theorem mem_range' {n} : m ∈ range' s n step ↔ ∃ i < n, m = s + step * i := by
  simp [range']
  constructor
  · rintro ⟨⟨i, w⟩, h, h'⟩
    exact ⟨i, w, by simp_all⟩
  · rintro ⟨i, w, h'⟩
    exact ⟨⟨i, w⟩, by simp_all⟩

theorem pop_range' : (range' s n step).pop = range' s (n - 1) step := by
  ext <;> simp

theorem map_add_range' (a) (s n step) : map (a + ·) (range' s n step) = range' (a + s) n step := by
  ext <;> simp <;> omega

theorem range'_succ_left : range' (s + 1) n step = (range' s n step).map (· + 1) := by
  ext <;> simp <;> omega

theorem range'_append (s m n step : Nat) :
    range' s m step ++ range' (s + step * m) n step = range' s (m + n) step := by
  ext i h₁ h₂
  · simp
  · simp only [size_append, size_range'] at h₁ h₂
    simp only [getElem_append, size_range', getElem_range', Nat.mul_sub_left_distrib, dite_eq_ite,
      ite_eq_left_iff, Nat.not_lt]
    intro h
    have : step * m ≤ step * i := by exact mul_le_mul_left step h
    omega

@[simp] theorem range'_append_1 (s m n : Nat) :
    range' s m ++ range' (s + m) n = range' s (m + n) := by simpa using range'_append s m n 1

theorem range'_concat (s n : Nat) : range' s (n + 1) step = range' s n step ++ #[s + step * n] := by
  exact (range'_append s n 1 step).symm

theorem range'_1_concat (s n : Nat) : range' s (n + 1) = range' s n ++ #[s + n] := by
  simp [range'_concat]

@[simp] theorem mem_range'_1 : m ∈ range' s n ↔ s ≤ m ∧ m < s + n := by
  simp [mem_range']; exact ⟨
    fun ⟨i, h, e⟩ => e ▸ ⟨Nat.le_add_right .., Nat.add_lt_add_left h _⟩,
    fun ⟨h₁, h₂⟩ => ⟨m - s, Nat.sub_lt_left_of_lt_add h₁ h₂, (Nat.add_sub_cancel' h₁).symm⟩⟩

theorem map_sub_range' (a s n : Nat) (h : a ≤ s) :
    map (· - a) (range' s n step) = range' (s - a) n step := by
  conv => lhs; rw [← Nat.add_sub_cancel' h]
  rw [← map_add_range', map_map, (?_ : _∘_ = _), map_id]
  funext x; apply Nat.add_sub_cancel_left

@[simp] theorem range'_eq_singleton_iff {s n a : Nat} : range' s n = #[a] ↔ s = a ∧ n = 1 := by
  rw [← toList_inj]
  simp

theorem range'_eq_append_iff : range' s n = xs ++ ys ↔ ∃ k, k ≤ n ∧ xs = range' s k ∧ ys = range' (s + k) (n - k) := by
  simp [← toList_inj, List.range'_eq_append_iff]

@[simp] theorem find?_range'_eq_some {s n : Nat} {i : Nat} {p : Nat → Bool} :
    (range' s n).find? p = some i ↔ p i ∧ i ∈ range' s n ∧ ∀ j, s ≤ j → j < i → !p j := by
  rw [← List.toArray_range']
  simp only [List.find?_toArray, mem_toArray]
  simp [List.find?_range'_eq_some]

@[simp] theorem find?_range'_eq_none {s n : Nat} {p : Nat → Bool} :
    (range' s n).find? p = none ↔ ∀ i, s ≤ i → i < s + n → !p i := by
  rw [← List.toArray_range']
  simp only [List.find?_toArray]
  simp

theorem erase_range' :
    (range' s n).erase i =
      range' s (min n (i - s)) ++ range' (max s (i + 1)) (min s (i + 1) + n - (i + 1)) := by
  simp only [← List.toArray_range', List.erase_toArray]
  simp [List.erase_range']

/-! ### range -/

theorem range_eq_range' (n : Nat) : range n = range' 0 n := by
  simp [range, range']

theorem range_succ_eq_map (n : Nat) : range (n + 1) = #[0] ++ map succ (range n) := by
  ext i h₁ h₂
  · simp
    omega
  · simp only [getElem_range, getElem_append, List.size_toArray, List.length_cons, List.length_nil,
      Nat.zero_add, lt_one_iff, List.getElem_toArray, List.getElem_singleton, getElem_map,
      succ_eq_add_one, dite_eq_ite]
    split <;> omega

theorem range'_eq_map_range (s n : Nat) : range' s n = map (s + ·) (range n) := by
  rw [range_eq_range', map_add_range']; rfl

@[simp] theorem range_eq_empty_iff {n : Nat} : range n = #[] ↔ n = 0 := by
  rw [← size_eq_zero_iff, size_range]

theorem range_ne_empty_iff {n : Nat} : range n ≠ #[] ↔ n ≠ 0 := by
  cases n <;> simp

theorem range_succ (n : Nat) : range (succ n) = range n ++ #[n] := by
  ext i h₁ h₂
  · simp
  · simp only [succ_eq_add_one, size_range] at h₁
    simp only [succ_eq_add_one, getElem_range, append_singleton, getElem_push, size_range,
      dite_eq_ite]
    split <;> omega

theorem range_add (a b : Nat) : range (a + b) = range a ++ (range b).map (a + ·) := by
  rw [← range'_eq_map_range]
  simpa [range_eq_range', Nat.add_comm] using (range'_append_1 0 a b).symm

theorem reverse_range' (s n : Nat) : reverse (range' s n) = map (s + n - 1 - ·) (range n) := by
  simp [← toList_inj, List.reverse_range']

@[simp]
theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]

theorem not_mem_range_self {n : Nat} : n ∉ range n := by simp

theorem self_mem_range_succ (n : Nat) : n ∈ range (n + 1) := by simp

@[simp] theorem take_range (m n : Nat) : take (range n) m = range (min m n) := by
  ext <;> simp

@[simp] theorem find?_range_eq_some {n : Nat} {i : Nat} {p : Nat → Bool} :
    (range n).find? p = some i ↔ p i ∧ i ∈ range n ∧ ∀ j, j < i → !p j := by
  simp [range_eq_range']

@[simp] theorem find?_range_eq_none {n : Nat} {p : Nat → Bool} :
    (range n).find? p = none ↔ ∀ i, i < n → !p i := by
  simp only [← List.toArray_range, List.find?_toArray, List.find?_range_eq_none]

theorem erase_range : (range n).erase i = range (min n i) ++ range' (i + 1) (n - (i + 1)) := by
  simp [range_eq_range', erase_range']


/-! ### zipIdx -/

@[simp]
theorem zipIdx_eq_empty_iff {xs : Array α} {i : Nat} : xs.zipIdx i = #[] ↔ xs = #[] := by
  cases xs
  simp

@[simp]
theorem getElem?_zipIdx (xs : Array α) (i j) : (zipIdx xs i)[j]? = xs[j]?.map fun a => (a, i + j) := by
  simp [getElem?_def]

theorem map_snd_add_zipIdx_eq_zipIdx (xs : Array α) (n k : Nat) :
    map (Prod.map id (· + n)) (zipIdx xs k) = zipIdx xs (n + k) :=
  ext_getElem? fun i ↦ by simp [(· ∘ ·), Nat.add_comm, Nat.add_left_comm]; rfl

@[simp]
theorem zipIdx_map_snd (i) (xs : Array α) : map Prod.snd (zipIdx xs i) = range' i xs.size := by
  cases xs
  simp

@[simp]
theorem zipIdx_map_fst (i) (xs : Array α) : map Prod.fst (zipIdx xs i) = xs := by
  cases xs
  simp

theorem zipIdx_eq_zip_range' (xs : Array α) {i : Nat} : xs.zipIdx i = xs.zip (range' i xs.size) := by
  simp [zip_of_prod (zipIdx_map_fst _ _) (zipIdx_map_snd _ _)]

@[simp]
theorem unzip_zipIdx_eq_prod (xs : Array α) {i : Nat} :
    (xs.zipIdx i).unzip = (xs, range' i xs.size) := by
  simp only [zipIdx_eq_zip_range', unzip_zip, size_range']

/-- Replace `zipIdx` with a starting index `n+1` with `zipIdx` starting from `n`,
followed by a `map` increasing the indices by one. -/
theorem zipIdx_succ (xs : Array α) (i : Nat) :
    xs.zipIdx (i + 1) = (xs.zipIdx i).map (fun ⟨a, j⟩ => (a, j + 1)) := by
  cases xs
  simp [List.zipIdx_succ]

/-- Replace `zipIdx` with a starting index with `zipIdx` starting from 0,
followed by a `map` increasing the indices. -/
theorem zipIdx_eq_map_add (xs : Array α) (i : Nat) :
    xs.zipIdx i = (xs.zipIdx 0).map (fun ⟨a, j⟩ => (a, i + j)) := by
  cases xs
  simp only [zipIdx_toArray, List.map_toArray, mk.injEq]
  rw [List.zipIdx_eq_map_add]

@[simp]
theorem zipIdx_singleton (x : α) (k : Nat) : zipIdx #[x] k = #[(x, k)] :=
  rfl

theorem mk_add_mem_zipIdx_iff_getElem? {k i : Nat} {x : α} {xs : Array α} :
    (x, k + i) ∈ zipIdx xs k ↔ xs[i]? = some x := by
  simp [mem_iff_getElem?, and_left_comm]

theorem le_snd_of_mem_zipIdx {x : α × Nat} {k : Nat} {xs : Array α} (h : x ∈ zipIdx xs k) :
    k ≤ x.2 :=
  (mk_mem_zipIdx_iff_le_and_getElem?_sub.1 h).1

theorem snd_lt_add_of_mem_zipIdx {x : α × Nat} {k : Nat} {xs : Array α} (h : x ∈ zipIdx xs k) :
    x.2 < k + xs.size := by
  rcases mem_iff_getElem.1 h with ⟨i, h', rfl⟩
  simpa using h'

theorem snd_lt_of_mem_zipIdx {x : α × Nat} {k : Nat} {xs : Array α} (h : x ∈ zipIdx xs k) : x.2 < xs.size + k := by
  simpa [Nat.add_comm] using snd_lt_add_of_mem_zipIdx h

theorem map_zipIdx (f : α → β) (xs : Array α) (k : Nat) :
    map (Prod.map f id) (zipIdx xs k) = zipIdx (xs.map f) k := by
  cases xs
  simp [List.map_zipIdx]

theorem fst_mem_of_mem_zipIdx {x : α × Nat} {xs : Array α} {k : Nat} (h : x ∈ zipIdx xs k) : x.1 ∈ xs :=
  zipIdx_map_fst k xs ▸ mem_map_of_mem _ h

theorem fst_eq_of_mem_zipIdx {x : α × Nat} {xs : Array α} {k : Nat} (h : x ∈ zipIdx xs k) :
    x.1 = xs[x.2 - k]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) := by
  cases xs
  exact List.fst_eq_of_mem_zipIdx (by simpa using h)

theorem mem_zipIdx {x : α} {i : Nat} {xs : Array α} {k : Nat} (h : (x, i) ∈ xs.zipIdx k) :
    k ≤ i ∧ i < k + xs.size ∧
      x = xs[i - k]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) :=
  ⟨le_snd_of_mem_zipIdx h, snd_lt_add_of_mem_zipIdx h, fst_eq_of_mem_zipIdx h⟩

/-- Variant of `mem_zipIdx` specialized at `k = 0`. -/
theorem mem_zipIdx' {x : α} {i : Nat} {xs : Array α} (h : (x, i) ∈ xs.zipIdx) :
    i < xs.size ∧ x = xs[i]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) :=
  ⟨by simpa using snd_lt_add_of_mem_zipIdx h, fst_eq_of_mem_zipIdx h⟩

theorem zipIdx_map (xs : Array α) (k : Nat) (f : α → β) :
    zipIdx (xs.map f) k = (zipIdx xs k).map (Prod.map f id) := by
  cases xs
  simp [List.zipIdx_map]

theorem zipIdx_append (xs ys : Array α) (k : Nat) :
    zipIdx (xs ++ ys) k = zipIdx xs k ++ zipIdx ys (k + xs.size) := by
  cases xs
  cases ys
  simp [List.zipIdx_append]

theorem zipIdx_eq_append_iff {xs : Array α} {k : Nat} :
    zipIdx xs k = ys ++ zs ↔
      ∃ ys' zs', xs = ys' ++ zs' ∧ ys = zipIdx ys' k ∧ zs = zipIdx zs' (k + ys'.size) := by
  rcases xs with ⟨xs⟩
  rcases ys with ⟨ys⟩
  rcases zs with ⟨zs⟩
  simp only [zipIdx_toArray, List.append_toArray, mk.injEq, List.zipIdx_eq_append_iff,
    toArray_eq_append_iff]
  constructor
  · rintro ⟨l₁', l₂', rfl, rfl, rfl⟩
    exact ⟨⟨l₁'⟩, ⟨l₂'⟩, by simp⟩
  · rintro ⟨⟨l₁'⟩, ⟨l₂'⟩, rfl, h⟩
    simp only [zipIdx_toArray, mk.injEq, List.size_toArray] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨l₁', l₂', by simp⟩

end Array
