/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Range
import Init.Data.List.Pairwise

/-!
# Lemmas about `List.range` and `List.enum`
-/

namespace List

open Nat

/-! ## Ranges and enumeration -/

/-! ### range' -/

theorem range'_succ (s n step) : range' s (n + 1) step = s :: range' (s + step) n step := by
  simp [range', Nat.add_succ, Nat.mul_succ]

@[simp] theorem length_range' (s step) : ∀ n : Nat, length (range' s n step) = n
  | 0 => rfl
  | _ + 1 => congrArg succ (length_range' _ _ _)

@[simp] theorem range'_eq_nil : range' s n step = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range']

theorem range'_ne_nil (s n : Nat) : range' s n ≠ [] ↔ n ≠ 0 := by
  cases n <;> simp

@[simp] theorem range'_zero : range' s 0 = [] := by
  simp

@[simp] theorem range'_one {s step : Nat} : range' s 1 step = [s] := rfl

theorem mem_range' : ∀{n}, m ∈ range' s n step ↔ ∃ i < n, m = s + step * i
  | 0 => by simp [range', Nat.not_lt_zero]
  | n + 1 => by
    have h (i) : i ≤ n ↔ i = 0 ∨ ∃ j, i = succ j ∧ j < n := by
      cases i <;> simp [Nat.succ_le, Nat.succ_inj']
    simp [range', mem_range', Nat.lt_succ, h]; simp only [← exists_and_right, and_assoc]
    rw [exists_comm]; simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

@[simp] theorem mem_range'_1 : m ∈ range' s n ↔ s ≤ m ∧ m < s + n := by
  simp [mem_range']; exact ⟨
    fun ⟨i, h, e⟩ => e ▸ ⟨Nat.le_add_right .., Nat.add_lt_add_left h _⟩,
    fun ⟨h₁, h₂⟩ => ⟨m - s, Nat.sub_lt_left_of_lt_add h₁ h₂, (Nat.add_sub_cancel' h₁).symm⟩⟩

theorem head?_range' (n : Nat) : (range' s n).head? = if n = 0 then none else some s := by
  induction n <;> simp_all [range'_succ, head?_append]

@[simp] theorem head_range' (n : Nat) (h) : (range' s n).head h = s := by
  repeat simp_all [head?_range']

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
  | succ n => simp [getLast?_range']

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

@[simp]
theorem map_add_range' (a) : ∀ s n step, map (a + ·) (range' s n step) = range' (a + s) n step
  | _, 0, _ => rfl
  | s, n + 1, step => by simp [range', map_add_range' _ (s + step) n step, Nat.add_assoc]

theorem map_sub_range' (a s n : Nat) (h : a ≤ s) :
    map (· - a) (range' s n step) = range' (s - a) n step := by
  conv => lhs; rw [← Nat.add_sub_cancel' h]
  rw [← map_add_range', map_map, (?_ : _∘_ = _), map_id]
  funext x; apply Nat.add_sub_cancel_left

theorem range'_append : ∀ s m n step : Nat,
    range' s m step ++ range' (s + step * m) n step = range' s (n + m) step
  | s, 0, n, step => rfl
  | s, m + 1, n, step => by
    simpa [range', Nat.mul_succ, Nat.add_assoc, Nat.add_comm]
      using range'_append (s + step) m n step

@[simp] theorem range'_append_1 (s m n : Nat) :
    range' s m ++ range' (s + m) n = range' s (n + m) := by simpa using range'_append s m n 1

theorem range'_sublist_right {s m n : Nat} : range' s m step <+ range' s n step ↔ m ≤ n :=
  ⟨fun h => by simpa only [length_range'] using h.length_le,
   fun h => by rw [← Nat.sub_add_cancel h, ← range'_append]; apply sublist_append_left⟩

theorem range'_subset_right {s m n : Nat} (step0 : 0 < step) :
    range' s m step ⊆ range' s n step ↔ m ≤ n := by
  refine ⟨fun h => Nat.le_of_not_lt fun hn => ?_, fun h => (range'_sublist_right.2 h).subset⟩
  have ⟨i, h', e⟩ := mem_range'.1 <| h <| mem_range'.2 ⟨_, hn, rfl⟩
  exact Nat.ne_of_gt h' (Nat.eq_of_mul_eq_mul_left step0 (Nat.add_left_cancel e))

theorem range'_subset_right_1 {s m n : Nat} : range' s m ⊆ range' s n ↔ m ≤ n :=
  range'_subset_right (by decide)

theorem getElem?_range' (s step) :
    ∀ {m n : Nat}, m < n → (range' s n step)[m]? = some (s + step * m)
  | 0, n + 1, _ => by simp [range'_succ]
  | m + 1, n + 1, h => by
    simp only [range'_succ, getElem?_cons_succ]
    exact (getElem?_range' (s + step) step (Nat.lt_of_add_lt_add_right h)).trans <| by
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

@[simp] theorem getElem_range' {n m step} (i) (H : i < (range' n m step).length) :
    (range' n m step)[i] = n + step * i :=
  (getElem?_eq_some.1 <| getElem?_range' n step (by simpa using H)).2

theorem range'_concat (s n : Nat) : range' s (n + 1) step = range' s n step ++ [s + step * n] := by
  rw [Nat.add_comm n 1]; exact (range'_append s n 1 step).symm

theorem range'_1_concat (s n : Nat) : range' s (n + 1) = range' s n ++ [s + n] := by
  simp [range'_concat]

/-! ### range -/

theorem range_loop_range' : ∀ s n : Nat, range.loop s (range' s n) = range' 0 (n + s)
  | 0, n => rfl
  | s + 1, n => by rw [← Nat.add_assoc, Nat.add_right_comm n s 1]; exact range_loop_range' s (n + 1)

theorem range_eq_range' (n : Nat) : range n = range' 0 n :=
  (range_loop_range' n 0).trans <| by rw [Nat.zero_add]

theorem range_succ_eq_map (n : Nat) : range (n + 1) = 0 :: map succ (range n) := by
  rw [range_eq_range', range_eq_range', range', Nat.add_comm, ← map_add_range']
  congr; exact funext (Nat.add_comm 1)

theorem reverse_range' : ∀ s n : Nat, reverse (range' s n) = map (s + n - 1 - ·) (range n)
  | s, 0 => rfl
  | s, n + 1 => by
    rw [range'_1_concat, reverse_append, range_succ_eq_map,
      show s + (n + 1) - 1 = s + n from rfl, map, map_map]
    simp [reverse_range', Nat.sub_right_comm, Nat.sub_sub]

theorem range'_eq_map_range (s n : Nat) : range' s n = map (s + ·) (range n) := by
  rw [range_eq_range', map_add_range']; rfl

@[simp] theorem length_range (n : Nat) : length (range n) = n := by
  simp only [range_eq_range', length_range']

@[simp] theorem range_eq_nil {n : Nat} : range n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range]

theorem range_ne_nil (n : Nat) : range n ≠ [] ↔ n ≠ 0 := by
  cases n <;> simp

@[simp]
theorem range_sublist {m n : Nat} : range m <+ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_sublist_right]

@[simp]
theorem range_subset {m n : Nat} : range m ⊆ range n ↔ m ≤ n := by
  simp only [range_eq_range', range'_subset_right, lt_succ_self]

@[simp]
theorem mem_range {m n : Nat} : m ∈ range n ↔ m < n := by
  simp only [range_eq_range', mem_range'_1, Nat.zero_le, true_and, Nat.zero_add]

theorem not_mem_range_self {n : Nat} : n ∉ range n := by simp

theorem self_mem_range_succ (n : Nat) : n ∈ range (n + 1) := by simp

theorem pairwise_lt_range (n : Nat) : Pairwise (· < ·) (range n) := by
  simp (config := {decide := true}) only [range_eq_range', pairwise_lt_range']

theorem pairwise_le_range (n : Nat) : Pairwise (· ≤ ·) (range n) :=
  Pairwise.imp Nat.le_of_lt (pairwise_lt_range _)

theorem getElem?_range {m n : Nat} (h : m < n) : (range n)[m]? = some m := by
  simp [range_eq_range', getElem?_range' _ _ h]

@[simp] theorem getElem_range {n : Nat} (m) (h : m < (range n).length) : (range n)[m] = m := by
  simp [range_eq_range']

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
  | succ n => simp [head?_range]

theorem getLast?_range (n : Nat) : (range n).getLast? = if n = 0 then none else some (n - 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [range_succ, getLast?_append, ih]
    split <;> simp_all

@[simp] theorem getLast_range (n : Nat) (h) : (range n).getLast h = n - 1 := by
  cases n with
  | zero => simp at h
  | succ n => simp [getLast?_range]

theorem take_range (m n : Nat) : take m (range n) = range (min m n) := by
  apply List.ext_getElem
  · simp
  · simp (config := { contextual := true }) [← getElem_take, Nat.lt_min]

theorem nodup_range (n : Nat) : Nodup (range n) := by
  simp (config := {decide := true}) only [range_eq_range', nodup_range']

/-! ### iota -/

theorem iota_eq_reverse_range' : ∀ n : Nat, iota n = reverse (range' 1 n)
  | 0 => rfl
  | n + 1 => by simp [iota, range'_concat, iota_eq_reverse_range' n, reverse_append, Nat.add_comm]

@[simp] theorem length_iota (n : Nat) : length (iota n) = n := by simp [iota_eq_reverse_range']

@[simp] theorem iota_eq_nil (n : Nat) : iota n = [] ↔ n = 0 := by
  cases n <;> simp

theorem iota_ne_nil (n : Nat) : iota n ≠ [] ↔ n ≠ 0 := by
  cases n <;> simp

@[simp]
theorem mem_iota {m n : Nat} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := by
  simp [iota_eq_reverse_range', Nat.add_comm, Nat.lt_succ]

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

@[simp]
theorem enumFrom_map_fst (n) :
    ∀ (l : List α), map Prod.fst (enumFrom n l) = range' n l.length
  | [] => rfl
  | _ :: _ => congrArg (cons _) (enumFrom_map_fst _ _)

@[simp]
theorem enumFrom_map_snd : ∀ (n) (l : List α), map Prod.snd (enumFrom n l) = l
  | _, [] => rfl
  | _, _ :: _ => congrArg (cons _) (enumFrom_map_snd _ _)

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

theorem enumFrom_cons' (n : Nat) (x : α) (xs : List α) :
    enumFrom n (x :: xs) = (n, x) :: (enumFrom n xs).map (Prod.map (· + 1) id) := by
  rw [enumFrom_cons, Nat.add_comm, ← map_fst_add_enumFrom_eq_enumFrom]

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

theorem enumFrom_eq_zip_range' (l : List α) {n : Nat} : l.enumFrom n = (range' n l.length).zip l :=
  zip_of_prod (enumFrom_map_fst _ _) (enumFrom_map_snd _ _)

@[simp]
theorem unzip_enumFrom_eq_prod (l : List α) {n : Nat} :
    (l.enumFrom n).unzip = (range' n l.length, l) := by
  simp only [enumFrom_eq_zip_range', unzip_zip, length_range']

/-! ### enum -/

theorem enum_cons : (a::as).enum = (0, a) :: as.enumFrom 1 := rfl

theorem enum_cons' (x : α) (xs : List α) :
    enum (x :: xs) = (0, x) :: (enum xs).map (Prod.map (· + 1) id) :=
  enumFrom_cons' _ _ _

@[simp]
theorem enum_eq_nil {l : List α} : List.enum l = [] ↔ l = [] := enumFrom_eq_nil

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

end List
