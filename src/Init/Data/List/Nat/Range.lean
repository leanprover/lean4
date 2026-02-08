/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
public import Init.Data.Nat.Lemmas
public import Init.Ext
import Init.ByCases
import Init.Data.List.Erase
import Init.Data.List.Find
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Range
import Init.Data.List.Zip
import Init.Data.Nat.Dvd
import Init.Data.Option.Lemmas
import Init.Omega
import Init.TacticsExtra

public section

/-!
# Lemmas about `List.range` and `List.enum`
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

/-! ## Ranges and enumeration -/

/-! ### range' -/

@[simp, grind =] theorem mem_range'_1 : m ∈ range' s n ↔ s ≤ m ∧ m < s + n := by
  simp [mem_range']; exact ⟨
    fun ⟨i, h, e⟩ => e ▸ ⟨Nat.le_add_right .., Nat.add_lt_add_left h _⟩,
    fun ⟨h₁, h₂⟩ => ⟨m - s, Nat.sub_lt_left_of_lt_add h₁ h₂, (Nat.add_sub_cancel' h₁).symm⟩⟩

@[grind =]
theorem getLast?_range' {n : Nat} : (range' s n).getLast? = if n = 0 then none else some (s + n - 1) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [range'_succ, getLast?_cons, ih]
    by_cases h : n = 0
    · rw [if_pos h]
      simp [h]
    · rw [if_neg h]
      simp

@[simp, grind =] theorem getLast_range' {n : Nat} (h) : (range' s n).getLast h = s + n - 1 := by
  cases n with
  | zero => simp at h
  | succ n => simp [getLast?_range', getLast_eq_iff_getLast?_eq_some]

theorem pairwise_lt_range' {s n} (step := 1) (pos : 0 < step := by simp) :
    Pairwise (· < ·) (range' s n step) :=
  match s, n, step, pos with
  | _, 0, _, _ => Pairwise.nil
  | s, n + 1, step, pos => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intro n m
      rw [mem_range'] at m
      omega
    · exact pairwise_lt_range' (s := s + step) step pos

theorem pairwise_le_range' {s n} (step := 1) :
    Pairwise (· ≤ ·) (range' s n step) :=
  match s, n, step with
  | _, 0, _ => Pairwise.nil
  | s, n + 1, step => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intro n m
      rw [mem_range'] at m
      omega
    · exact pairwise_le_range' (s := s + step) step

theorem nodup_range' {s n : Nat} (step := 1) (h : 0 < step := by simp) : Nodup (range' s n step) :=
  (pairwise_lt_range' step h).imp Nat.ne_of_lt

theorem map_sub_range' {a s : Nat} (h : a ≤ s) (n : Nat) :
    map (· - a) (range' s n step) = range' (s - a) n step := by
  conv => lhs; rw [← Nat.add_sub_cancel' h]
  rw [← map_add_range', map_map, (?_ : _∘_ = _), map_id]
  funext x; apply Nat.add_sub_cancel_left

@[simp] theorem range'_eq_singleton_iff {s n a : Nat} : range' s n = [a] ↔ s = a ∧ n = 1 := by
  rw [range'_eq_cons_iff]
  simp only [nil_eq, range'_eq_nil_iff, and_congr_right_iff]
  rintro rfl
  omega

theorem range'_eq_append_iff : range' s n step = xs ++ ys ↔ ∃ k, k ≤ n ∧ xs = range' s k step ∧ ys = range' (s + k * step) (n - k) step := by
  induction n generalizing s xs ys with
  | zero => simp
  | succ n ih =>
    simp only [range'_succ]
    rw [cons_eq_append_iff]
    have add_mul' (k n m : Nat) : (n + m) * k = m * k + n * k := by rw [Nat.add_mul]; omega
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨_, rfl, h⟩)
      · exact ⟨0, by simp [range'_succ]⟩
      · simp only [ih] at h
        obtain ⟨k, h, rfl, rfl⟩ := h
        refine ⟨k + 1, ?_⟩
        simp_all [range'_succ, Nat.add_assoc, (by omega : n + 1 - (k + 1) = n - k)]
    · rintro ⟨k, h, rfl, rfl⟩
      cases k with
      | zero => simp [range'_succ]
      | succ k =>
        simp only [range'_succ, reduceCtorEq, false_and, cons.injEq, true_and, ih, exists_eq_left', false_or]
        refine ⟨k, ?_⟩
        simp_all [Nat.add_assoc, (by omega : n + 1 - (k + 1) = n - k)]

@[simp] theorem find?_range'_eq_some {s n : Nat} {i : Nat} {p : Nat → Bool} :
    (range' s n).find? p = some i ↔ p i ∧ i ∈ range' s n ∧ ∀ j, s ≤ j → j < i → !p j := by
  rw [find?_eq_some_iff_append]
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, exists_and_right, mem_range'_1,
    and_congr_right_iff]
  simp only [range'_eq_append_iff, eq_comm (a := i :: _), range'_eq_cons_iff]
  intro h
  constructor
  · rintro ⟨as, ⟨_, k, h₁, rfl, rfl, h₂, rfl⟩, h₃⟩
    constructor
    · omega
    · simpa using h₃
  · rintro ⟨⟨h₁, h₂⟩, h₃⟩
    refine ⟨range' s (i - s), ⟨⟨range' (i + 1) (n - (i - s) - 1), i - s, ?_⟩ , ?_⟩⟩
    · simp; omega
    · simp only [mem_range'_1, and_imp]
      intro a a₁ a₂
      exact h₃ a a₁ (by omega)

theorem find?_range'_eq_none {s n : Nat} {p : Nat → Bool} :
    (range' s n).find? p = none ↔ ∀ i, s ≤ i → i < s + n → !p i := by
  simp

theorem erase_range' :
    (range' s n).erase i =
      range' s (min n (i - s)) ++ range' (max s (i + 1)) (min s (i + 1) + n - (i + 1)) := by
  by_cases h : i ∈ range' s n
  · obtain ⟨as, bs, h₁, h₂⟩ := eq_append_cons_of_mem h
    rw [h₁, erase_append_right _ h₂, erase_cons_head]
    rw [range'_eq_append_iff] at h₁
    obtain ⟨k, -, rfl, hbs⟩ := h₁
    rw [eq_comm, range'_eq_cons_iff] at hbs
    obtain ⟨rfl, -, rfl⟩ := hbs
    simp at h
    congr 2 <;> omega
  · rw [erase_of_not_mem h]
    simp only [mem_range'_1, not_and, Nat.not_lt] at h
    by_cases h' : s ≤ i
    · have p : min s (i + 1) + n - (i + 1) = 0 := by omega
      simp [p]
      omega
    · have p : i - s = 0 := by omega
      simp [p]
      omega

@[simp, grind =]
theorem count_range' {a s n step} (h : 0 < step := by simp) :
    count a (range' s n step) = if ∃ i, i < n ∧ a = s + step * i then 1 else 0 := by
  rw [(nodup_range' step h).count]
  simp only [mem_range']

@[simp, grind =]
theorem count_range_1' {a s n} :
    count a (range' s n) = if s ≤ a ∧ a < s + n then 1 else 0 := by
  rw [count_range' (by simp)]
  split <;> rename_i h
  · obtain ⟨i, h, rfl⟩ := h
    simp [h]
  · simp at h
    rw [if_neg]
    simp only [not_and, Nat.not_lt]
    intro w
    specialize h (a - s)
    omega

@[simp, grind =]
theorem sum_range' : (range' start n step).sum = n * start + n * (n - 1) * step / 2 := by
  induction n generalizing start with
  | zero => simp
  | succ n ih =>
    simp_all only [List.range'_succ, List.sum_cons, Nat.mul_add, ← Nat.add_assoc,
      Nat.add_mul, Nat.one_mul, Nat.add_one_sub_one]
    have : n * step + n * (n - 1) * step / 2 = (n * n * step + n * step) / 2 := by
      apply Nat.eq_div_of_mul_eq_left (by omega)
      rw [Nat.add_mul, Nat.div_mul_cancel]
      · calc  n * step * 2 + n * (n - 1) * step
          _ = n * step * 2 + n * step * (n - 1) := by simp [Nat.mul_comm, Nat.mul_assoc]
          _ = n * step + n * step * n := by cases n <;> simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]
          _ = n * n * step + n * step := by simp [Nat.mul_comm, Nat.add_comm, Nat.mul_left_comm]
      · have : 2 ∣ n ∨ 2 ∣ (n - 1) := by omega
        apply Nat.dvd_mul_right_of_dvd
        apply Nat.dvd_mul.mpr
        cases this with
        | inl h => exists 2, 1; omega
        | inr h => exists 1, 2; omega
    omega

@[simp, grind =]
theorem drop_range' : (List.range' start n step).drop k = List.range' (start + k * step) (n - k) step := by
  induction k generalizing start n with
  | zero => simp
  | succ =>
    cases n
    · simp [*, Nat.add_mul, ← Nat.add_assoc, Nat.add_right_comm]
    · simp only [range'_succ, drop_succ_cons, Nat.add_mul, Nat.one_mul, ← Nat.add_assoc,
      Nat.add_right_comm, *]
      rename_i n₁ _ n₂
      rw [(by omega : n₂ + 1 - (n₁ + 1) = n₂ - n₁)]

@[simp, grind =]
theorem take_range'_of_length_le (h : n ≤ k) : (List.range' start n step).take k = List.range' start n step := by
  induction n generalizing start k with
  | zero => simp
  | succ n ih => cases k <;> simp_all [List.range'_succ]

@[simp, grind =]
theorem take_range'_of_length_ge (h : n ≥ k) : (List.range' start n step).take k = List.range' start k step := by
  induction k generalizing start n with
  | zero => simp
  | succ k ih => cases n <;> simp_all [List.range'_succ]

/-! ### range -/

theorem reverse_range' : ∀ {s n : Nat}, reverse (range' s n) = map (s + n - 1 - ·) (range n)
  | _, 0 => rfl
  | s, n + 1 => by
    rw [range'_1_concat, reverse_append, range_succ_eq_map,
      show s + (n + 1) - 1 = s + n from rfl, map, map_map]
    simp [reverse_range', Nat.sub_right_comm, Nat.sub_sub]

@[simp, grind =]
theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]

theorem not_mem_range_self {n : Nat} : n ∉ range n := by simp

theorem self_mem_range_succ {n : Nat} : n ∈ range (n + 1) := by simp

theorem pairwise_lt_range {n : Nat} : Pairwise (· < ·) (range n) := by
  simp +decide only [range_eq_range', pairwise_lt_range']

theorem pairwise_le_range {n : Nat} : Pairwise (· ≤ ·) (range n) :=
  Pairwise.imp Nat.le_of_lt pairwise_lt_range

@[simp, grind =] theorem take_range {i n : Nat} : take i (range n) = range (min i n) := by
  apply List.ext_getElem
  · simp
  · simp +contextual [getElem_take, Nat.lt_min]

theorem nodup_range {n : Nat} : Nodup (range n) := by
  simp +decide only [range_eq_range', nodup_range']

@[simp] theorem find?_range_eq_some {n : Nat} {i : Nat} {p : Nat → Bool} :
    (range n).find? p = some i ↔ p i ∧ i ∈ range n ∧ ∀ j, j < i → !p j := by
  simp [range_eq_range']

theorem find?_range_eq_none {n : Nat} {p : Nat → Bool} :
    (range n).find? p = none ↔ ∀ i, i < n → !p i := by
  simp

theorem erase_range : (range n).erase i = range (min n i) ++ range' (i + 1) (n - (i + 1)) := by
  simp [range_eq_range', erase_range']

@[simp, grind =]
theorem count_range {a n} :
    count a (range n) = if a < n then 1 else 0 := by
  rw [range_eq_range', count_range_1']
  simp

/-! ### zipIdx -/

@[simp, grind =]
theorem zipIdx_singleton {x : α} {k : Nat} : zipIdx [x] k = [(x, k)] :=
  rfl

@[simp, grind =] theorem head?_zipIdx {l : List α} {k : Nat} :
    (zipIdx l k).head? = l.head?.map fun a => (a, k) := by
  simp [head?_eq_getElem?]

@[simp, grind =] theorem getLast?_zipIdx {l : List α} {k : Nat} :
    (zipIdx l k).getLast? = l.getLast?.map fun a => (a, k + l.length - 1) := by
  simp [getLast?_eq_getElem?]
  cases l <;> simp

theorem mk_add_mem_zipIdx_iff_getElem? {k i : Nat} {x : α} {l : List α} :
    (x, k + i) ∈ zipIdx l k ↔ l[i]? = some x := by
  simp [mem_iff_getElem?, and_left_comm]

theorem mk_mem_zipIdx_iff_le_and_getElem?_sub {k i : Nat} {x : α} {l : List α} :
    (x, i) ∈ zipIdx l k ↔ k ≤ i ∧ l[i - k]? = some x := by
  if h : k ≤ i then
    rcases Nat.exists_eq_add_of_le h with ⟨i, rfl⟩
    simp [mk_add_mem_zipIdx_iff_getElem?, Nat.add_sub_cancel_left]
  else
    have : ∀ m, k + m ≠ i := by rintro _ rfl; simp at h
    simp [h, mem_iff_getElem?, this]

/-- Variant of `mk_mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mk_mem_zipIdx_iff_getElem? {i : Nat} {x : α} {l : List α} : (x, i) ∈ zipIdx l ↔ l[i]? = some x := by
  simp [mk_mem_zipIdx_iff_le_and_getElem?_sub]

@[grind =]
theorem mem_zipIdx_iff_le_and_getElem?_sub {x : α × Nat} {l : List α} {k : Nat} :
    x ∈ zipIdx l k ↔ k ≤ x.2 ∧ l[x.2 - k]? = some x.1 := by
  cases x
  simp [mk_mem_zipIdx_iff_le_and_getElem?_sub]

/-- Variant of `mem_zipIdx_iff_le_and_getElem?_sub` specialized at `k = 0`,
to avoid the inequality and the subtraction. -/
theorem mem_zipIdx_iff_getElem? {x : α × Nat} {l : List α} : x ∈ zipIdx l ↔ l[x.2]? = some x.1 := by
  cases x
  simp [mk_mem_zipIdx_iff_le_and_getElem?_sub]

theorem le_snd_of_mem_zipIdx {x : α × Nat} {k : Nat} {l : List α} (h : x ∈ zipIdx l k) :
    k ≤ x.2 :=
  (mk_mem_zipIdx_iff_le_and_getElem?_sub.1 h).1

theorem snd_lt_add_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat} (h : x ∈ zipIdx l k) :
    x.2 < k + length l := by
  rcases mem_iff_get.1 h with ⟨i, rfl⟩
  simpa using i.isLt

theorem snd_lt_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat} (h : x ∈ l.zipIdx k) : x.2 < l.length + k := by
  simpa [Nat.add_comm] using snd_lt_add_of_mem_zipIdx h

theorem map_zipIdx {f : α → β} {l : List α} {k : Nat} :
    map (Prod.map f id) (zipIdx l k) = zipIdx (l.map f) k := by
  induction l generalizing k <;> simp_all

theorem fst_mem_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat} (h : x ∈ zipIdx l k) : x.1 ∈ l :=
  zipIdx_map_fst k l ▸ mem_map_of_mem h

theorem fst_eq_of_mem_zipIdx {x : α × Nat} {l : List α} {k : Nat} (h : x ∈ zipIdx l k) :
    x.1 = l[x.2 - k]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) := by
  induction l generalizing k with
  | nil => cases h
  | cons hd tl ih =>
    cases h with
    | head _ => simp
    | tail h m =>
      specialize ih m
      have : x.2 - k = x.2 - (k + 1) + 1 := by
        have := le_snd_of_mem_zipIdx m
        omega
      simp [this, ih]

theorem mem_zipIdx {x : α} {i : Nat} {xs : List α} {k : Nat} (h : (x, i) ∈ xs.zipIdx k) :
    k ≤ i ∧ i < k + xs.length ∧
      x = xs[i - k]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) :=
  ⟨le_snd_of_mem_zipIdx h, snd_lt_add_of_mem_zipIdx h, fst_eq_of_mem_zipIdx h⟩

/-- Variant of `mem_zipIdx` specialized at `k = 0`. -/
theorem mem_zipIdx' {x : α} {i : Nat} {xs : List α} (h : (x, i) ∈ xs.zipIdx) :
    i < xs.length ∧ x = xs[i]'(by have := le_snd_of_mem_zipIdx h; have := snd_lt_add_of_mem_zipIdx h; omega) :=
  ⟨by simpa using snd_lt_add_of_mem_zipIdx h, fst_eq_of_mem_zipIdx h⟩

theorem zipIdx_map {l : List α} {k : Nat} {f : α → β} :
    zipIdx (l.map f) k = (zipIdx l k).map (Prod.map f id) := by
  induction l with
  | nil => rfl
  | cons hd tl IH =>
    rw [map_cons, zipIdx_cons', zipIdx_cons', map_cons, map_map, IH, map_map]
    rfl

@[grind =]
theorem zipIdx_append {xs ys : List α} {k : Nat} :
    zipIdx (xs ++ ys) k = zipIdx xs k ++ zipIdx ys (k + xs.length) := by
  induction xs generalizing ys k with
  | nil => simp
  | cons x xs IH =>
    rw [cons_append, zipIdx_cons, IH, ← cons_append, ← zipIdx_cons, length, Nat.add_right_comm,
      Nat.add_assoc]

theorem zipIdx_eq_cons_iff {l : List α} {k : Nat} :
    zipIdx l k = x :: l' ↔ ∃ a as, l = a :: as ∧ x = (a, k) ∧ l' = zipIdx as (k + 1) := by
  rw [zipIdx_eq_zip_range', zip_eq_cons_iff]
  constructor
  · rintro ⟨l₁, l₂, rfl, h, rfl⟩
    rw [range'_eq_cons_iff] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨x.1, l₁, by simp [zipIdx_eq_zip_range']⟩
  · rintro ⟨a, as, rfl, rfl, rfl⟩
    refine ⟨as, range' (k+1) as.length, ?_⟩
    simp [zipIdx_eq_zip_range', range'_succ]

theorem zipIdx_eq_append_iff {l : List α} {k : Nat} :
    zipIdx l k = l₁ ++ l₂ ↔
      ∃ l₁' l₂', l = l₁' ++ l₂' ∧ l₁ = zipIdx l₁' k ∧ l₂ = zipIdx l₂' (k + l₁'.length) := by
  rw [zipIdx_eq_zip_range', zip_eq_append_iff]
  constructor
  · rintro ⟨ws, xs, ys, zs, h, rfl, h', rfl, rfl⟩
    rw [range'_eq_append_iff] at h'
    obtain ⟨k, -, rfl, rfl⟩ := h'
    simp only [length_range'] at h
    obtain rfl := h
    refine ⟨ws, xs, rfl, ?_⟩
    simp [zipIdx_eq_zip_range', length_append]
  · rintro ⟨l₁', l₂', rfl, rfl, rfl⟩
    simp only [zipIdx_eq_zip_range']
    refine ⟨l₁', l₂', range' k l₁'.length, range' (k + l₁'.length) l₂'.length, ?_⟩
    simp

end List
