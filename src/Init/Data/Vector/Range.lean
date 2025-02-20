/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Vector.Lemmas
import Init.Data.Vector.Zip
import Init.Data.Vector.MapIdx
import Init.Data.Array.Range

/-!
# Lemmas about `Vector.range'`, `Vector.range`, and `Vector.zipIdx`

-/

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

open Nat

/-! ## Ranges and enumeration -/

/-! ### range' -/

@[simp] theorem toArray_range' (start size step) :
    (range' start size step).toArray = Array.range' start size step := by
  rfl

theorem range'_eq_mk_range' (start size step) :
    range' start size step = Vector.mk (Array.range' start size step) (by simp) := by
  rfl

@[simp] theorem getElem_range' (start size step i) (h : i < size) :
   (range' start size step)[i] = start + step * i := by
  simp [range', h]

@[simp] theorem getElem?_range' (start size step i) :
   (range' start size step)[i]? = if i < size then some (start + step * i) else none := by
  simp [getElem?_def, range']

theorem range'_succ (s n step) :
    range' s (n + 1) step = (#v[s] ++ range' (s + step) n step).cast (by omega) := by
  rw [← toArray_inj]
  simp [Array.range'_succ]

theorem range'_zero : range' s 0 step = #v[] := by
  simp

@[simp] theorem range'_one {s step : Nat} : range' s 1 step = #v[s] := rfl

@[simp] theorem range'_inj : range' s n = range' s' n ↔ (n = 0 ∨ s = s') := by
  rw [← toArray_inj]
  simp [List.range'_inj]

theorem mem_range' {n} : m ∈ range' s n step ↔ ∃ i < n, m = s + step * i := by
  simp [range', Array.mem_range']

theorem pop_range' : (range' s n step).pop = range' s (n - 1) step := by
  ext <;> simp

theorem map_add_range' (a) (s n step) : map (a + ·) (range' s n step) = range' (a + s) n step := by
  ext <;> simp <;> omega

theorem range'_succ_left : range' (s + 1) n step = (range' s n step).map (· + 1) := by
  ext <;> simp <;> omega

theorem range'_append (s m n step : Nat) :
    range' s m step ++ range' (s + step * m) n step = range' s (m + n) step := by
  rw [← toArray_inj]
  simp [Array.range'_append]

@[simp] theorem range'_append_1 (s m n : Nat) :
    range' s m ++ range' (s + m) n = range' s (m + n) := by simpa using range'_append s m n 1

theorem range'_concat (s n : Nat) : range' s (n + 1) step = range' s n step ++ #v[s + step * n] := by
  exact (range'_append s n 1 step).symm

theorem range'_1_concat (s n : Nat) : range' s (n + 1) = range' s n ++ #v[s + n] := by
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

theorem range'_eq_append_iff : range' s (n + m) = xs ++ ys ↔ xs = range' s n ∧ ys = range' (s + n) m := by
  simp only [← toArray_inj, toArray_range', toArray_append, Array.range'_eq_append_iff]
  constructor
  · rintro ⟨k, hk, h₁, h₂⟩
    have w : k = n := by
      replace h₁ := congrArg Array.size h₁
      simp_all
    subst w
    simp_all
    omega
  · rintro ⟨h₁, h₂⟩
    exact ⟨n, by omega, by simp_all; omega⟩

@[simp] theorem find?_range'_eq_some {s n : Nat} {i : Nat} {p : Nat → Bool} :
    (range' s n).find? p = some i ↔ p i ∧ i ∈ range' s n ∧ ∀ j, s ≤ j → j < i → !p j := by
  simp [range'_eq_mk_range']

@[simp] theorem find?_range'_eq_none {s n : Nat} {p : Nat → Bool} :
    (range' s n).find? p = none ↔ ∀ i, s ≤ i → i < s + n → !p i := by
  simp [range'_eq_mk_range']

/-! ### range -/

theorem range_eq_range' (n : Nat) : range n = range' 0 n := by
  simp [range, range', Array.range_eq_range']

theorem range_succ_eq_map (n : Nat) : range (n + 1) =
    (#v[0] ++ map succ (range n)).cast (by omega) := by
  rw [← toArray_inj]
  simp [Array.range_succ_eq_map]

theorem range'_eq_map_range (s n : Nat) : range' s n = map (s + ·) (range n) := by
  rw [range_eq_range', map_add_range']; rfl

theorem range_succ (n : Nat) : range (succ n) = range n ++ #v[n] := by
  rw [← toArray_inj]
  simp [Array.range_succ]

theorem range_add (n m : Nat) : range (n + m) = range n ++ (range m).map (n + ·) := by
  rw [← range'_eq_map_range]
  simpa [range_eq_range', Nat.add_comm] using (range'_append_1 0 n m).symm

theorem reverse_range' (s n : Nat) : reverse (range' s n) = map (s + n - 1 - ·) (range n) := by
  simp [← toList_inj, List.reverse_range']

@[simp]
theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]

theorem not_mem_range_self {n : Nat} : n ∉ range n := by simp

theorem self_mem_range_succ (n : Nat) : n ∈ range (n + 1) := by simp

@[simp] theorem take_range (n i : Nat) : take (range n) i = range (min i n) := by
  ext <;> simp
  erw [getElem_extract] -- Why is an `erw` needed here? This should be by simp!
  simp

@[simp] theorem find?_range_eq_some {n : Nat} {i : Nat} {p : Nat → Bool} :
    (range n).find? p = some i ↔ p i ∧ i ∈ range n ∧ ∀ j, j < i → !p j := by
  simp [range_eq_range']

@[simp] theorem find?_range_eq_none {n : Nat} {p : Nat → Bool} :
    (range n).find? p = none ↔ ∀ i, i < n → !p i := by
  simp [range_eq_range']

/-! ### zipIdx -/

@[simp]
theorem getElem?_zipIdx (xs : Vector α n) (i j) : (zipIdx xs i)[j]? = xs[j]?.map fun a => (a, i + j) := by
  simp [getElem?_def]

theorem map_snd_add_zipIdx_eq_zipIdx (xs : Vector α n) (m k : Nat) :
    map (Prod.map id (· + m)) (zipIdx xs k) = zipIdx xs (m + k) := by
  ext <;> simp <;> omega

@[simp]
theorem zipIdx_map_snd (i) (xs : Vector α n) : map Prod.snd (zipIdx xs i) = range' i n := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.zipIdx_map_snd]

@[simp]
theorem zipIdx_map_fst (i) (xs : Vector α n) : map Prod.fst (zipIdx xs i) = xs := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.zipIdx_map_fst]

theorem zipIdx_eq_zip_range' (xs : Vector α n) : xs.zipIdx i = xs.zip (range' i n) := by
  simp [zip_of_prod (zipIdx_map_fst _ _) (zipIdx_map_snd _ _)]

@[simp]
theorem unzip_zipIdx_eq_prod (xs : Vector α n) {i : Nat} :
    (xs.zipIdx i).unzip = (xs, range' i n) := by
  simp only [zipIdx_eq_zip_range', unzip_zip]

/-- Replace `zipIdx` with a starting index `i+1` with `zipIdx` starting from `i`,
followed by a `map` increasing the indices by one. -/
theorem zipIdx_succ (xs : Vector α n) (i : Nat) :
    xs.zipIdx (i + 1) = (xs.zipIdx i).map (fun ⟨a, i⟩ => (a, i + 1)) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.zipIdx_succ]

/-- Replace `zipIdx` with a starting index with `zipIdx` starting from 0,
followed by a `map` increasing the indices. -/
theorem zipIdx_eq_map_add (xs : Vector α n) (i : Nat) :
    xs.zipIdx i = xs.zipIdx.map (fun ⟨a, j⟩ => (a, i + j)) := by
  rcases xs with ⟨xs, rfl⟩
  simp only [zipIdx_mk, map_mk, eq_mk]
  rw [Array.zipIdx_eq_map_add]

@[simp]
theorem zipIdx_singleton (x : α) (k : Nat) : zipIdx #v[x] k = #v[(x, k)] :=
  rfl

theorem mk_add_mem_zipIdx_iff_getElem? {k i : Nat} {x : α} {xs : Vector α n} :
    (x, k + i) ∈ zipIdx xs k ↔ xs[i]? = some x := by
  simp [mem_iff_getElem?, and_left_comm]

theorem le_snd_of_mem_zipIdx {x : α × Nat} {k : Nat} {xs : Vector α n} (h : x ∈ zipIdx xs k) :
    k ≤ x.2 :=
  (mk_mem_zipIdx_iff_le_and_getElem?_sub.1 h).1

theorem snd_lt_add_of_mem_zipIdx {x : α × Nat} {k : Nat} {xs : Vector α n} (h : x ∈ zipIdx xs k) :
    x.2 < k + n := by
  rcases mem_iff_getElem.1 h with ⟨i, h', rfl⟩
  simpa using h'

theorem snd_lt_of_mem_zipIdx {x : α × Nat} {k : Nat} {xs : Vector α n} (h : x ∈ zipIdx xs k) :
    x.2 < n + k := by
  simpa [Nat.add_comm] using snd_lt_add_of_mem_zipIdx h

theorem map_zipIdx (f : α → β) (xs : Vector α n) (k : Nat) :
    map (Prod.map f id) (zipIdx xs k) = zipIdx (xs.map f) k := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.map_zipIdx]

theorem fst_mem_of_mem_zipIdx {x : α × Nat} {xs : Vector α n} {k : Nat} (h : x ∈ zipIdx xs k) : x.1 ∈ xs :=
  zipIdx_map_fst k xs ▸ mem_map_of_mem _ h

theorem fst_eq_of_mem_zipIdx {x : α × Nat} {xs : Vector α n} {k : Nat} (h : x ∈ zipIdx xs k) :
    x.1 = xs[x.2 - k]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) := by
  cases xs
  exact Array.fst_eq_of_mem_zipIdx (by simpa using h)

theorem mem_zipIdx {x : α} {i : Nat} {xs : Vector α n} {k : Nat} (h : (x, i) ∈ xs.zipIdx k) :
    k ≤ i ∧ i < k + n ∧
      x = xs[i - k]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) :=
  ⟨le_snd_of_mem_zipIdx h, snd_lt_add_of_mem_zipIdx h, fst_eq_of_mem_zipIdx h⟩

/-- Variant of `mem_zipIdx` specialized at `k = 0`. -/
theorem mem_zipIdx' {x : α} {i : Nat} {xs : Vector α n} (h : (x, i) ∈ xs.zipIdx) :
    i < n ∧ x = xs[i]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) :=
  ⟨by simpa using snd_lt_add_of_mem_zipIdx h, fst_eq_of_mem_zipIdx h⟩

theorem zipIdx_map (xs : Vector α n) (k : Nat) (f : α → β) :
    zipIdx (xs.map f) k = (zipIdx xs k).map (Prod.map f id) := by
  rcases xs with ⟨xs, rfl⟩
  simp [Array.zipIdx_map]

theorem zipIdx_append (xs : Vector α n) (ys : Vector α m) (k : Nat) :
    zipIdx (xs ++ ys) k = zipIdx xs k ++ zipIdx ys (k + n) := by
  rcases xs with ⟨xs, rfl⟩
  rcases ys with ⟨ys, rfl⟩
  simp [Array.zipIdx_append]

theorem zipIdx_eq_append_iff {xs : Vector α (n + m)} {k : Nat} :
    zipIdx xs k = ys ++ zs ↔
      ∃ (ys' : Vector α n) (zs' : Vector α m),
        xs = ys' ++ zs' ∧ ys = zipIdx ys' k ∧ zs = zipIdx zs' (k + n) := by
  rcases xs with ⟨xs, h⟩
  rcases ys with ⟨ys, rfl⟩
  rcases zs with ⟨zs, rfl⟩
  simp only [zipIdx_mk, mk_append_mk, eq_mk, Array.zipIdx_eq_append_iff, mk_eq, toArray_append,
    toArray_zipIdx]
  constructor
  · rintro ⟨ys', zs', rfl, rfl, rfl⟩
    exact ⟨⟨ys', by simp⟩, ⟨zs', by simp⟩, by simp⟩
  · rintro ⟨⟨ys', h₁⟩, ⟨zs', h₂⟩, rfl, w₁, w₂⟩
    exact ⟨ys', zs', by simp, w₁, by simp [h₁, w₂]⟩

end Vector
