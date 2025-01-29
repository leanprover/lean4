/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Array.Lemmas
import Init.Data.List.Nat.Range

/-!
# Lemmas about `Array.range` and `Array.zipIdx`

-/

namespace Array

open Nat

/-! ## Ranges and enumeration -/

/-! ### range' -/

theorem range'_succ (s n step) : range' s (n + 1) step = #[s] ++ range' (s + step) n step := by
  rw [← toList_inj]
  simp [List.range'_succ]

@[simp] theorem range'_eq_empty : range' s n step = #[] ↔ n = 0 := by
  rw [← size_eq_zero, size_range']

theorem range'_ne_empty (s : Nat) {n step : Nat} : range' s n step ≠ #[] ↔ n ≠ 0 := by
  cases n <;> simp

@[simp] theorem range'_zero : range' s 0 step = #[] := by
  simp

@[simp] theorem range'_one {s step : Nat} : range' s 1 step = #[s] := rfl

@[simp] theorem range'_inj : range' s n = range' s' n' ↔ n = n' ∧ (n = 0 ∨ s = s') := by
  rw [← toList_inj]
  simp [List.range'_inj]

theorem mem_range' {n} : m ∈ range' s n step ↔ ∃ i < n, m = s + step * i := by
  simp [range']

theorem pop_range' := sorry
theorem back_range' := sorry

theorem map_add_range' (a) : ∀ s n step, map (a + ·) (range' s n step) = range' (a + s) n step
  | _, 0, _ => rfl
  | s, n + 1, step => by simp [range', map_add_range' _ (s + step) n step, Nat.add_assoc]

theorem range'_succ_left : range' (s + 1) n step = (range' s n step).map (· + 1) := by
  apply ext_getElem
  · simp
  · simp [Nat.add_right_comm]

theorem range'_append : ∀ s m n step : Nat,
    range' s m step ++ range' (s + step * m) n step = range' s (n + m) step
  | _, 0, _, _ => rfl
  | s, m + 1, n, step => by
    simpa [range', Nat.mul_succ, Nat.add_assoc, Nat.add_comm]
      using range'_append (s + step) m n step

@[simp] theorem range'_append_1 (s m n : Nat) :
    range' s m ++ range' (s + m) n = range' s (n + m) := by simpa using range'_append s m n 1

theorem range'_concat (s n : Nat) : range' s (n + 1) step = range' s n step ++ [s + step * n] := by
  rw [Nat.add_comm n 1]; exact (range'_append s n 1 step).symm

theorem range'_1_concat (s n : Nat) : range' s (n + 1) = range' s n ++ [s + n] := by
  simp [range'_concat]

theorem range'_eq_cons_iff : range' s n = a :: xs ↔ s = a ∧ 0 < n ∧ xs = range' (a + 1) (n - 1) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    simp only [range'_succ]
    simp only [cons.injEq, and_congr_right_iff]
    rintro rfl
    simp [eq_comm]

/-! ### range -/

theorem range_eq_range' (n : Nat) : range n = range' 0 n := by
  simp [range, range']

theorem range_succ_eq_map (n : Nat) : range (n + 1) = 0 :: map succ (range n) := by
  rw [range_eq_range', range_eq_range', range', Nat.add_comm, ← map_add_range']
  congr; exact funext (Nat.add_comm 1)

theorem range'_eq_map_range (s n : Nat) : range' s n = map (s + ·) (range n) := by
  rw [range_eq_range', map_add_range']; rfl

@[simp] theorem length_range (n : Nat) : length (range n) = n := by
  simp only [range_eq_range', length_range']

@[simp] theorem range_eq_nil {n : Nat} : range n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range]

theorem range_ne_nil {n : Nat} : range n ≠ [] ↔ n ≠ 0 := by
  cases n <;> simp

@[simp] theorem tail_range (n : Nat) : (range n).tail = range' 1 (n - 1) := by
  rw [range_eq_range', tail_range']

@[simp]
theorem range_sublist {m n : Nat} : range m <+ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_sublist_right]

@[simp]
theorem range_subset {m n : Nat} : range m ⊆ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_subset_right, lt_succ_self]

theorem range_succ (n : Nat) : range (succ n) = range n ++ [n] := by
  simp only [range_eq_range', range'_1_concat, Nat.zero_add]

theorem range_add (a b : Nat) : range (a + b) = range a ++ (range b).map (a + ·) := by
  rw [← range'_eq_map_range]
  simpa [range_eq_range', Nat.add_comm] using (range'_append_1 0 a b).symm

theorem head?_range (n : Nat) : (range n).head? = if n = 0 then none else some 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [range_succ, head?_append, ih]
    split <;> simp_all

@[simp] theorem head_range (n : Nat) (h) : (range n).head h = 0 := by
  cases n with
  | zero => simp at h
  | succ n => simp [head?_range, head_eq_iff_head?_eq_some]

theorem getLast?_range (n : Nat) : (range n).getLast? = if n = 0 then none else some (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [range_succ, getLast?_append, ih]
    split <;> simp_all

@[simp] theorem getLast_range (n : Nat) (h) : (range n).getLast h = n - 1 := by
  cases n with
  | zero => simp at h
  | succ n => simp [getLast?_range, getLast_eq_iff_getLast_eq_some]

/-! ### zipIdx -/

@[simp]
theorem zipIdx_eq_nil_iff {l : List α} {n : Nat} : List.zipIdx l n = [] ↔ l = [] := by
  cases l <;> simp

@[simp] theorem length_zipIdx : ∀ {l : List α} {n}, (zipIdx l n).length = l.length
  | [], _ => rfl
  | _ :: _, _ => congrArg Nat.succ length_zipIdx

@[simp]
theorem getElem?_zipIdx :
    ∀ (l : List α) n m, (zipIdx l n)[m]? = l[m]?.map fun a => (a, n + m)
  | [], _, _ => rfl
  | _ :: _, _, 0 => by simp
  | _ :: l, n, m + 1 => by
    simp only [zipIdx_cons, getElem?_cons_succ]
    exact (getElem?_zipIdx l (n + 1) m).trans <| by rw [Nat.add_right_comm]; rfl

@[simp]
theorem getElem_zipIdx (l : List α) (n) (i : Nat) (h : i < (l.zipIdx n).length) :
    (l.zipIdx n)[i] = (l[i]'(by simpa [length_zipIdx] using h), n + i) := by
  simp only [length_zipIdx] at h
  rw [getElem_eq_getElem?_get]
  simp only [getElem?_zipIdx, getElem?_eq_getElem h]
  simp

@[simp]
theorem tail_zipIdx (l : List α) (n : Nat) : (zipIdx l n).tail = zipIdx l.tail (n + 1) := by
  induction l generalizing n with
  | nil => simp
  | cons _ l ih => simp [ih, zipIdx_cons]

theorem map_snd_add_zipIdx_eq_zipIdx (l : List α) (n k : Nat) :
    map (Prod.map id (· + n)) (zipIdx l k) = zipIdx l (n + k) :=
  ext_getElem? fun i ↦ by simp [(· ∘ ·), Nat.add_comm, Nat.add_left_comm]; rfl

theorem zipIdx_cons' (n : Nat) (x : α) (xs : List α) :
    zipIdx (x :: xs) n = (x, n) :: (zipIdx xs n).map (Prod.map id (· + 1)) := by
  rw [zipIdx_cons, Nat.add_comm, ← map_snd_add_zipIdx_eq_zipIdx]

@[simp]
theorem zipIdx_map_snd (n) :
    ∀ (l : List α), map Prod.snd (zipIdx l n) = range' n l.length
  | [] => rfl
  | _ :: _ => congrArg (cons _) (zipIdx_map_snd _ _)

@[simp]
theorem zipIdx_map_fst : ∀ (n) (l : List α), map Prod.fst (zipIdx l n) = l
  | _, [] => rfl
  | _, _ :: _ => congrArg (cons _) (zipIdx_map_fst _ _)

theorem zipIdx_eq_zip_range' (l : List α) {n : Nat} : l.zipIdx n = l.zip (range' n l.length) :=
  zip_of_prod (zipIdx_map_fst _ _) (zipIdx_map_snd _ _)

@[simp]
theorem unzip_zipIdx_eq_prod (l : List α) {n : Nat} :
    (l.zipIdx n).unzip = (l, range' n l.length) := by
  simp only [zipIdx_eq_zip_range', unzip_zip, length_range']

/-- Replace `zipIdx` with a starting index `n+1` with `zipIdx` starting from `n`,
followed by a `map` increasing the indices by one. -/
theorem zipIdx_succ (l : List α) (n : Nat) :
    l.zipIdx (n + 1) = (l.zipIdx n).map (fun ⟨a, i⟩ => (a, i + 1)) := by
  induction l generalizing n with
  | nil => rfl
  | cons _ _ ih => simp only [zipIdx_cons, ih (n + 1), map_cons]

/-- Replace `zipIdx` with a starting index with `zipIdx` starting from 0,
followed by a `map` increasing the indices. -/
theorem zipIdx_eq_map_add (l : List α) (n : Nat) :
    l.zipIdx n = l.zipIdx.map (fun ⟨a, i⟩ => (a, n + i)) := by
  induction l generalizing n with
  | nil => rfl
  | cons _ _ ih => simp [ih (n+1), zipIdx_succ, Nat.add_assoc, Nat.add_comm 1]

end Array
