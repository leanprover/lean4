/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Range
import Init.Data.List.Pairwise
import Init.Data.List.Find
import Init.Data.List.Erase

/-!
# Lemmas about `List.range` and `List.enum`
-/

namespace List

open Nat

/-! ## Ranges and enumeration -/

/-! ### range' -/

@[simp] theorem mem_range'_1 : m ∈ range' s n ↔ s ≤ m ∧ m < s + n := by
  simp [mem_range']; exact ⟨
    fun ⟨i, h, e⟩ => e ▸ ⟨Nat.le_add_right .., Nat.add_lt_add_left h _⟩,
    fun ⟨h₁, h₂⟩ => ⟨m - s, Nat.sub_lt_left_of_lt_add h₁ h₂, (Nat.add_sub_cancel' h₁).symm⟩⟩

theorem getLast?_range' (n : Nat) : (range' s n).getLast? = if n = 0 then none else some (s + n - 1) := by
  induction n generalizing s with
  | zero => simp
  | succ n ih =>
    rw [range'_succ, getLast?_cons, ih]
    by_cases h : n = 0
    · rw [if_pos h]
      simp [h]
    · rw [if_neg h]
      simp
      omega

@[simp] theorem getLast_range' (n : Nat) (h) : (range' s n).getLast h = s + n - 1 := by
  cases n with
  | zero => simp at h
  | succ n => simp [getLast?_range', getLast_eq_iff_getLast_eq_some]

theorem pairwise_lt_range' s n (step := 1) (pos : 0 < step := by simp) :
    Pairwise (· < ·) (range' s n step) :=
  match s, n, step, pos with
  | _, 0, _, _ => Pairwise.nil
  | s, n + 1, step, pos => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intros n m
      rw [mem_range'] at m
      omega
    · exact pairwise_lt_range' (s + step) n step pos

theorem pairwise_le_range' s n (step := 1) :
    Pairwise (· ≤ ·) (range' s n step) :=
  match s, n, step with
  | _, 0, _ => Pairwise.nil
  | s, n + 1, step => by
    simp only [range'_succ, pairwise_cons]
    constructor
    · intros n m
      rw [mem_range'] at m
      omega
    · exact pairwise_le_range' (s + step) n step

theorem nodup_range' (s n : Nat) (step := 1) (h : 0 < step := by simp) : Nodup (range' s n step) :=
  (pairwise_lt_range' s n step h).imp Nat.ne_of_lt

theorem map_sub_range' (a s n : Nat) (h : a ≤ s) :
    map (· - a) (range' s n step) = range' (s - a) n step := by
  conv => lhs; rw [← Nat.add_sub_cancel' h]
  rw [← map_add_range', map_map, (?_ : _∘_ = _), map_id]
  funext x; apply Nat.add_sub_cancel_left

@[simp] theorem range'_eq_singleton {s n a : Nat} : range' s n = [a] ↔ s = a ∧ n = 1 := by
  rw [range'_eq_cons_iff]
  simp only [nil_eq, range'_eq_nil, and_congr_right_iff]
  rintro rfl
  omega

theorem range'_eq_append_iff : range' s n = xs ++ ys ↔ ∃ k, k ≤ n ∧ xs = range' s k ∧ ys = range' (s + k) (n - k) := by
  induction n generalizing s xs ys with
  | zero => simp
  | succ n ih =>
    simp only [range'_succ]
    rw [cons_eq_append_iff]
    constructor
    · rintro (⟨rfl, rfl⟩ | ⟨a, rfl, h⟩)
      · exact ⟨0, by simp [range'_succ]⟩
      · simp only [ih] at h
        obtain ⟨k, h, rfl, rfl⟩ := h
        refine ⟨k + 1, ?_⟩
        simp_all [range'_succ]
        omega
    · rintro ⟨k, h, rfl, rfl⟩
      cases k with
      | zero => simp [range'_succ]
      | succ k =>
        simp only [range'_succ, reduceCtorEq, false_and, cons.injEq, true_and, ih, range'_inj, exists_eq_left', or_true, and_true, false_or]
        refine ⟨k, ?_⟩
        simp_all
        omega

@[simp] theorem find?_range'_eq_some {s n : Nat} {i : Nat} {p : Nat → Bool} :
    (range' s n).find? p = some i ↔ p i ∧ i ∈ range' s n ∧ ∀ j, s ≤ j → j < i → !p j := by
  rw [find?_eq_some_iff_append]
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, exists_and_right, mem_range'_1,
    and_congr_right_iff]
  simp only [range'_eq_append_iff, eq_comm (a := i :: _), range'_eq_cons_iff]
  intro h
  constructor
  · rintro ⟨as, ⟨x, k, h₁, rfl, rfl, h₂, rfl⟩, h₃⟩
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

/-! ### range -/

theorem reverse_range' : ∀ s n : Nat, reverse (range' s n) = map (s + n - 1 - ·) (range n)
  | _, 0 => rfl
  | s, n + 1 => by
    rw [range'_1_concat, reverse_append, range_succ_eq_map,
      show s + (n + 1) - 1 = s + n from rfl, map, map_map]
    simp [reverse_range', Nat.sub_right_comm, Nat.sub_sub]

@[simp]
theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]

theorem not_mem_range_self {n : Nat} : n ∉ range n := by simp

theorem self_mem_range_succ (n : Nat) : n ∈ range (n + 1) := by simp

theorem pairwise_lt_range (n : Nat) : Pairwise (· < ·) (range n) := by
  simp +decide only [range_eq_range', pairwise_lt_range']

theorem pairwise_le_range (n : Nat) : Pairwise (· ≤ ·) (range n) :=
  Pairwise.imp Nat.le_of_lt (pairwise_lt_range _)

theorem take_range (m n : Nat) : take m (range n) = range (min m n) := by
  apply List.ext_getElem
  · simp
  · simp +contextual [getElem_take, Nat.lt_min]

theorem nodup_range (n : Nat) : Nodup (range n) := by
  simp +decide only [range_eq_range', nodup_range']

@[simp] theorem find?_range_eq_some {n : Nat} {i : Nat} {p : Nat → Bool} :
    (range n).find? p = some i ↔ p i ∧ i ∈ range n ∧ ∀ j, j < i → !p j := by
  simp [range_eq_range']

theorem find?_range_eq_none {n : Nat} {p : Nat → Bool} :
    (range n).find? p = none ↔ ∀ i, i < n → !p i := by
  simp

theorem erase_range : (range n).erase i = range (min n i) ++ range' (i + 1) (n - (i + 1)) := by
  simp [range_eq_range', erase_range']

/-! ### iota -/

theorem iota_eq_reverse_range' : ∀ n : Nat, iota n = reverse (range' 1 n)
  | 0 => rfl
  | n + 1 => by simp [iota, range'_concat, iota_eq_reverse_range' n, reverse_append, Nat.add_comm]

@[simp] theorem length_iota (n : Nat) : length (iota n) = n := by simp [iota_eq_reverse_range']

@[simp] theorem iota_eq_nil {n : Nat} : iota n = [] ↔ n = 0 := by
  cases n <;> simp

theorem iota_ne_nil {n : Nat} : iota n ≠ [] ↔ n ≠ 0 := by
  cases n <;> simp

@[simp]
theorem mem_iota {m n : Nat} : m ∈ iota n ↔ 0 < m ∧ m ≤ n := by
  simp [iota_eq_reverse_range', Nat.add_comm, Nat.lt_succ]
  omega

@[simp] theorem iota_inj : iota n = iota n' ↔ n = n' := by
  constructor
  · intro h
    have h' := congrArg List.length h
    simp at h'
    exact h'
  · rintro rfl
    simp

theorem iota_eq_cons_iff : iota n = a :: xs ↔ n = a ∧ 0 < n ∧ xs = iota (n - 1) := by
  simp [iota_eq_reverse_range']
  simp [range'_eq_append_iff, reverse_eq_iff]
  constructor
  · rintro ⟨k, h, rfl, h'⟩
    rw [eq_comm, range'_eq_singleton] at h'
    simp only [reverse_inj, range'_inj, or_true, and_true]
    omega
  · rintro ⟨rfl, h, rfl⟩
    refine ⟨n - 1, by simp, rfl, ?_⟩
    rw [eq_comm, range'_eq_singleton]
    omega

theorem iota_eq_append_iff : iota n = xs ++ ys ↔ ∃ k, k ≤ n ∧ xs = (range' (k + 1) (n - k)).reverse ∧ ys = iota k := by
  simp only [iota_eq_reverse_range']
  rw [reverse_eq_append_iff]
  rw [range'_eq_append_iff]
  simp only [reverse_eq_iff]
  constructor
  · rintro ⟨k, h, rfl, rfl⟩
    simp; omega
  · rintro ⟨k, h, rfl, rfl⟩
    exact ⟨k, by simp; omega⟩

theorem pairwise_gt_iota (n : Nat) : Pairwise (· > ·) (iota n) := by
  simpa only [iota_eq_reverse_range', pairwise_reverse] using pairwise_lt_range' 1 n

theorem nodup_iota (n : Nat) : Nodup (iota n) :=
  (pairwise_gt_iota n).imp Nat.ne_of_gt

@[simp] theorem head?_iota (n : Nat) : (iota n).head? = if n = 0 then none else some n := by
  cases n <;> simp

@[simp] theorem head_iota (n : Nat) (h) : (iota n).head h = n := by
  cases n with
  | zero => simp at h
  | succ n => simp

@[simp] theorem tail_iota (n : Nat) : (iota n).tail = iota (n - 1) := by
  cases n <;> simp

@[simp] theorem reverse_iota : reverse (iota n) = range' 1 n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iota_succ, reverse_cons, ih, range'_1_concat, Nat.add_comm]

@[simp] theorem getLast?_iota (n : Nat) : (iota n).getLast? = if n = 0 then none else some 1 := by
  rw [getLast?_eq_head?_reverse]
  simp [head?_range']

@[simp] theorem getLast_iota (n : Nat) (h) : (iota n).getLast h = 1 := by
  rw [getLast_eq_head_reverse]
  simp

theorem find?_iota_eq_none {n : Nat} {p : Nat → Bool} :
    (iota n).find? p = none ↔ ∀ i, 0 < i → i ≤ n → !p i := by
  simp

@[simp] theorem find?_iota_eq_some {n : Nat} {i : Nat} {p : Nat → Bool} :
    (iota n).find? p = some i ↔ p i ∧ i ∈ iota n ∧ ∀ j, i < j → j ≤ n → !p j := by
  rw [find?_eq_some_iff_append]
  simp only [iota_eq_reverse_range', reverse_eq_append_iff, reverse_cons, append_assoc, cons_append,
    nil_append, Bool.not_eq_eq_eq_not, Bool.not_true, exists_and_right, mem_reverse, mem_range'_1,
    and_congr_right_iff]
  intro h
  constructor
  · rintro ⟨as, ⟨xs, h⟩, h'⟩
    constructor
    · replace h : i ∈ range' 1 n := by
        rw [h]
        exact mem_append_cons_self
      simpa using h
    · rw [range'_eq_append_iff] at h
      simp [reverse_eq_iff] at h
      obtain ⟨k, h₁, rfl, h₂⟩ := h
      rw [eq_comm, range'_eq_cons_iff, reverse_eq_iff] at h₂
      obtain ⟨rfl, -, rfl⟩ := h₂
      intro j j₁ j₂
      apply h'
      simp; omega
  · rintro ⟨⟨i₁, i₂⟩, h⟩
    refine ⟨(range' (i+1) (n-i)).reverse, ⟨(range' 1 (i-1)).reverse, ?_⟩, ?_⟩
    · simp [← range'_succ]
      rw [range'_eq_append_iff]
      refine ⟨i-1, ?_⟩
      constructor
      · omega
      · simp
        omega
    · simp
      intros a a₁ a₂
      apply h
      · omega
      · omega

/-! ### enumFrom -/

@[simp]
theorem enumFrom_singleton (x : α) (n : Nat) : enumFrom n [x] = [(n, x)] :=
  rfl

@[simp] theorem head?_enumFrom (n : Nat) (l : List α) :
    (enumFrom n l).head? = l.head?.map fun a => (n, a) := by
  simp [head?_eq_getElem?]

@[simp] theorem getLast?_enumFrom (n : Nat) (l : List α) :
    (enumFrom n l).getLast? = l.getLast?.map fun a => (n + l.length - 1, a) := by
  simp [getLast?_eq_getElem?]
  cases l <;> simp; omega

theorem mk_add_mem_enumFrom_iff_getElem? {n i : Nat} {x : α} {l : List α} :
    (n + i, x) ∈ enumFrom n l ↔ l[i]? = some x := by
  simp [mem_iff_get?]

theorem mk_mem_enumFrom_iff_le_and_getElem?_sub {n i : Nat} {x : α} {l : List α} :
    (i, x) ∈ enumFrom n l ↔ n ≤ i ∧ l[i - n]? = x := by
  if h : n ≤ i then
    rcases Nat.exists_eq_add_of_le h with ⟨i, rfl⟩
    simp [mk_add_mem_enumFrom_iff_getElem?, Nat.add_sub_cancel_left]
  else
    have : ∀ k, n + k ≠ i := by rintro k rfl; simp at h
    simp [h, mem_iff_get?, this]

theorem le_fst_of_mem_enumFrom {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) :
    n ≤ x.1 :=
  (mk_mem_enumFrom_iff_le_and_getElem?_sub.1 h).1

theorem fst_lt_add_of_mem_enumFrom {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) :
    x.1 < n + length l := by
  rcases mem_iff_get.1 h with ⟨i, rfl⟩
  simpa using i.isLt

theorem map_enumFrom (f : α → β) (n : Nat) (l : List α) :
    map (Prod.map id f) (enumFrom n l) = enumFrom n (map f l) := by
  induction l generalizing n <;> simp_all

theorem snd_mem_of_mem_enumFrom {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) : x.2 ∈ l :=
  enumFrom_map_snd n l ▸ mem_map_of_mem _ h

theorem snd_eq_of_mem_enumFrom {x : Nat × α} {n : Nat} {l : List α} (h : x ∈ enumFrom n l) :
    x.2 = l[x.1 - n]'(by have := le_fst_of_mem_enumFrom h; have := fst_lt_add_of_mem_enumFrom h; omega) := by
  induction l generalizing n with
  | nil => cases h
  | cons hd tl ih =>
    cases h with
    | head h => simp
    | tail h m =>
      specialize ih m
      have : x.1 - n = x.1 - (n + 1) + 1 := by
        have := le_fst_of_mem_enumFrom m
        omega
      simp [this, ih]

theorem mem_enumFrom {x : α} {i j : Nat} {xs : List α} (h : (i, x) ∈ xs.enumFrom j) :
    j ≤ i ∧ i < j + xs.length ∧
      x = xs[i - j]'(by have := le_fst_of_mem_enumFrom h; have := fst_lt_add_of_mem_enumFrom h; omega) :=
  ⟨le_fst_of_mem_enumFrom h, fst_lt_add_of_mem_enumFrom h, snd_eq_of_mem_enumFrom h⟩

theorem enumFrom_map (n : Nat) (l : List α) (f : α → β) :
    enumFrom n (l.map f) = (enumFrom n l).map (Prod.map id f) := by
  induction l with
  | nil => rfl
  | cons hd tl IH =>
    rw [map_cons, enumFrom_cons', enumFrom_cons', map_cons, map_map, IH, map_map]
    rfl

theorem enumFrom_append (xs ys : List α) (n : Nat) :
    enumFrom n (xs ++ ys) = enumFrom n xs ++ enumFrom (n + xs.length) ys := by
  induction xs generalizing ys n with
  | nil => simp
  | cons x xs IH =>
    rw [cons_append, enumFrom_cons, IH, ← cons_append, ← enumFrom_cons, length, Nat.add_right_comm,
      Nat.add_assoc]

theorem enumFrom_eq_cons_iff {l : List α} {n : Nat} :
    l.enumFrom n = x :: l' ↔ ∃ a as, l = a :: as ∧ x = (n, a) ∧ l' = enumFrom (n + 1) as := by
  rw [enumFrom_eq_zip_range', zip_eq_cons_iff]
  constructor
  · rintro ⟨l₁, l₂, h, rfl, rfl⟩
    rw [range'_eq_cons_iff] at h
    obtain ⟨rfl, -, rfl⟩ := h
    exact ⟨x.2, l₂, by simp [enumFrom_eq_zip_range']⟩
  · rintro ⟨a, as, rfl, rfl, rfl⟩
    refine ⟨range' (n+1) as.length, as, ?_⟩
    simp [enumFrom_eq_zip_range', range'_succ]

theorem enumFrom_eq_append_iff {l : List α} {n : Nat} :
    l.enumFrom n = l₁ ++ l₂ ↔
      ∃ l₁' l₂', l = l₁' ++ l₂' ∧ l₁ = l₁'.enumFrom n ∧ l₂ = l₂'.enumFrom (n + l₁'.length) := by
  rw [enumFrom_eq_zip_range', zip_eq_append_iff]
  constructor
  · rintro ⟨w, x, y, z, h, h', rfl, rfl, rfl⟩
    rw [range'_eq_append_iff] at h'
    obtain ⟨k, -, rfl, rfl⟩ := h'
    simp only [length_range'] at h
    obtain rfl := h
    refine ⟨y, z, rfl, ?_⟩
    simp only [enumFrom_eq_zip_range', length_append, true_and]
    congr
    omega
  · rintro ⟨l₁', l₂', rfl, rfl, rfl⟩
    simp only [enumFrom_eq_zip_range']
    refine ⟨range' n l₁'.length, range' (n + l₁'.length) l₂'.length, l₁', l₂', ?_⟩
    simp [Nat.add_comm]

/-! ### enum -/

@[simp]
theorem enum_eq_nil_iff {l : List α} : List.enum l = [] ↔ l = [] := enumFrom_eq_nil

@[deprecated enum_eq_nil_iff (since := "2024-11-04")]
theorem enum_eq_nil {l : List α} : List.enum l = [] ↔ l = [] := enum_eq_nil_iff

@[simp] theorem enum_singleton (x : α) : enum [x] = [(0, x)] := rfl

@[simp] theorem enum_length : (enum l).length = l.length :=
  enumFrom_length

@[simp]
theorem getElem?_enum (l : List α) (n : Nat) : (enum l)[n]? = l[n]?.map fun a => (n, a) := by
  rw [enum, getElem?_enumFrom, Nat.zero_add]

@[simp]
theorem getElem_enum (l : List α) (i : Nat) (h : i < l.enum.length) :
    l.enum[i] = (i, l[i]'(by simpa [enum_length] using h)) := by
  simp [enum]

@[simp] theorem head?_enum (l : List α) :
    l.enum.head? = l.head?.map fun a => (0, a) := by
  simp [head?_eq_getElem?]

@[simp] theorem getLast?_enum (l : List α) :
    l.enum.getLast? = l.getLast?.map fun a => (l.length - 1, a) := by
  simp [getLast?_eq_getElem?]

@[simp] theorem tail_enum (l : List α) : (enum l).tail = enumFrom 1 l.tail := by
  simp [enum]

theorem mk_mem_enum_iff_getElem? {i : Nat} {x : α} {l : List α} : (i, x) ∈ enum l ↔ l[i]? = x := by
  simp [enum, mk_mem_enumFrom_iff_le_and_getElem?_sub]

theorem mem_enum_iff_getElem? {x : Nat × α} {l : List α} : x ∈ enum l ↔ l[x.1]? = some x.2 :=
  mk_mem_enum_iff_getElem?

theorem fst_lt_of_mem_enum {x : Nat × α} {l : List α} (h : x ∈ enum l) : x.1 < length l := by
  simpa using fst_lt_add_of_mem_enumFrom h

theorem snd_mem_of_mem_enum {x : Nat × α} {l : List α} (h : x ∈ enum l) : x.2 ∈ l :=
  snd_mem_of_mem_enumFrom h

theorem snd_eq_of_mem_enum {x : Nat × α} {l : List α} (h : x ∈ enum l) :
    x.2 = l[x.1]'(fst_lt_of_mem_enum h) :=
  snd_eq_of_mem_enumFrom h

theorem mem_enum {x : α} {i : Nat} {xs : List α} (h : (i, x) ∈ xs.enum) :
    i < xs.length ∧ x = xs[i]'(fst_lt_of_mem_enum h) :=
  by simpa using mem_enumFrom h

theorem map_enum (f : α → β) (l : List α) : map (Prod.map id f) (enum l) = enum (map f l) :=
  map_enumFrom f 0 l

@[simp] theorem enum_map_fst (l : List α) : map Prod.fst (enum l) = range l.length := by
  simp only [enum, enumFrom_map_fst, range_eq_range']

@[simp]
theorem enum_map_snd (l : List α) : map Prod.snd (enum l) = l :=
  enumFrom_map_snd _ _

theorem enum_map (l : List α) (f : α → β) : (l.map f).enum = l.enum.map (Prod.map id f) :=
  enumFrom_map _ _ _

theorem enum_append (xs ys : List α) : enum (xs ++ ys) = enum xs ++ enumFrom xs.length ys := by
  simp [enum, enumFrom_append]

theorem enum_eq_zip_range (l : List α) : l.enum = (range l.length).zip l :=
  zip_of_prod (enum_map_fst _) (enum_map_snd _)

@[simp]
theorem unzip_enum_eq_prod (l : List α) : l.enum.unzip = (range l.length, l) := by
  simp only [enum_eq_zip_range, unzip_zip, length_range]

theorem enum_eq_cons_iff {l : List α} :
    l.enum = x :: l' ↔ ∃ a as, l = a :: as ∧ x = (0, a) ∧ l' = enumFrom 1 as := by
  rw [enum, enumFrom_eq_cons_iff]

theorem enum_eq_append_iff {l : List α} :
    l.enum = l₁ ++ l₂ ↔
      ∃ l₁' l₂', l = l₁' ++ l₂' ∧ l₁ = l₁'.enum ∧ l₂ = l₂'.enumFrom l₁'.length := by
  simp [enum, enumFrom_eq_append_iff]

end List
