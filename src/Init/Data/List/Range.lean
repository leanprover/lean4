/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Lemmas
import Init.Data.Nat.Lemmas

/-!
# Lemmas about `List.range` and `List.enum`
-/

namespace List

open Nat

/-! ## Ranges and enumeration -/

/-! ### range', range -/

theorem range'_succ (s n step) : range' s (n + 1) step = s :: range' (s + step) n step := by
  simp [range', Nat.add_succ, Nat.mul_succ]

@[simp] theorem length_range' (s step) : ∀ n : Nat, length (range' s n step) = n
  | 0 => rfl
  | _ + 1 => congrArg succ (length_range' _ _ _)

@[simp] theorem range'_eq_nil : range' s n step = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range']

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

theorem range_loop_range' : ∀ s n : Nat, range.loop s (range' s n) = range' 0 (n + s)
  | 0, n => rfl
  | s + 1, n => by rw [← Nat.add_assoc, Nat.add_right_comm n s 1]; exact range_loop_range' s (n + 1)

theorem range_eq_range' (n : Nat) : range n = range' 0 n :=
  (range_loop_range' n 0).trans <| by rw [Nat.zero_add]

theorem range_succ_eq_map (n : Nat) : range (n + 1) = 0 :: map succ (range n) := by
  rw [range_eq_range', range_eq_range', range', Nat.add_comm, ← map_add_range']
  congr; exact funext (Nat.add_comm 1)

theorem range'_eq_map_range (s n : Nat) : range' s n = map (s + ·) (range n) := by
  rw [range_eq_range', map_add_range']; rfl

@[simp] theorem length_range (n : Nat) : length (range n) = n := by
  simp only [range_eq_range', length_range']

@[simp] theorem range_eq_nil {n : Nat} : range n = [] ↔ n = 0 := by
  rw [← length_eq_zero, length_range]

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

theorem getElem?_range {m n : Nat} (h : m < n) : (range n)[m]? = some m := by
  simp [range_eq_range', getElem?_range' _ _ h]

@[simp] theorem getElem_range {n : Nat} (m) (h : m < (range n).length) : (range n)[m] = m := by
  simp [range_eq_range']

theorem range_succ (n : Nat) : range (succ n) = range n ++ [n] := by
  simp only [range_eq_range', range'_1_concat, Nat.zero_add]

theorem range_add (a b : Nat) : range (a + b) = range a ++ (range b).map (a + ·) := by
  rw [← range'_eq_map_range]
  simpa [range_eq_range', Nat.add_comm] using (range'_append_1 0 a b).symm

theorem iota_eq_reverse_range' : ∀ n : Nat, iota n = reverse (range' 1 n)
  | 0 => rfl
  | n + 1 => by simp [iota, range'_concat, iota_eq_reverse_range' n, reverse_append, Nat.add_comm]

@[simp] theorem length_iota (n : Nat) : length (iota n) = n := by simp [iota_eq_reverse_range']

@[simp]
theorem mem_iota {m n : Nat} : m ∈ iota n ↔ 1 ≤ m ∧ m ≤ n := by
  simp [iota_eq_reverse_range', Nat.add_comm, Nat.lt_succ]

theorem reverse_range' : ∀ s n : Nat, reverse (range' s n) = map (s + n - 1 - ·) (range n)
  | s, 0 => rfl
  | s, n + 1 => by
    rw [range'_1_concat, reverse_append, range_succ_eq_map,
      show s + (n + 1) - 1 = s + n from rfl, map, map_map]
    simp [reverse_range', Nat.sub_right_comm, Nat.sub_sub]

/-! ### enumFrom -/

@[simp]
theorem enumFrom_singleton (x : α) (n : Nat) : enumFrom n [x] = [(n, x)] :=
  rfl

@[simp]
theorem enumFrom_eq_nil {n : Nat} {l : List α} : List.enumFrom n l = [] ↔ l = [] := by
  cases l <;> simp

@[simp] theorem enumFrom_length : ∀ {n} {l : List α}, (enumFrom n l).length = l.length
  | _, [] => rfl
  | _, _ :: _ => congrArg Nat.succ enumFrom_length

@[simp]
theorem getElem?_enumFrom :
    ∀ n (l : List α) m, (enumFrom n l)[m]? = l[m]?.map fun a => (n + m, a)
  | n, [], m => rfl
  | n, a :: l, 0 => by simp
  | n, a :: l, m + 1 => by
    simp only [enumFrom_cons, getElem?_cons_succ]
    exact (getElem?_enumFrom (n + 1) l m).trans <| by rw [Nat.add_right_comm]; rfl

@[simp]
theorem getElem_enumFrom (l : List α) (n) (i : Nat) (h : i < (l.enumFrom n).length) :
    (l.enumFrom n)[i] = (n + i, l[i]'(by simpa [enumFrom_length] using h)) := by
  simp only [enumFrom_length] at h
  rw [getElem_eq_getElem?]
  simp only [getElem?_enumFrom, getElem?_eq_getElem h]
  simp

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

theorem mem_enumFrom {x : α} {i j : Nat} (xs : List α) (h : (i, x) ∈ xs.enumFrom j) :
    j ≤ i ∧ i < j + xs.length ∧ x ∈ xs :=
  ⟨le_fst_of_mem_enumFrom h, fst_lt_add_of_mem_enumFrom h, snd_mem_of_mem_enumFrom h⟩

theorem map_fst_add_enumFrom_eq_enumFrom (l : List α) (n k : Nat) :
    map (Prod.map (· + n) id) (enumFrom k l) = enumFrom (n + k) l :=
  ext_getElem? fun i ↦ by simp [(· ∘ ·), Nat.add_comm, Nat.add_left_comm]; rfl

theorem map_fst_add_enum_eq_enumFrom (l : List α) (n : Nat) :
    map (Prod.map (· + n) id) (enum l) = enumFrom n l :=
  map_fst_add_enumFrom_eq_enumFrom l _ _

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

theorem mk_mem_enum_iff_getElem? {i : Nat} {x : α} {l : List α} : (i, x) ∈ enum l ↔ l[i]? = x := by
  simp [enum, mk_mem_enumFrom_iff_le_and_getElem?_sub]

theorem mem_enum_iff_getElem? {x : Nat × α} {l : List α} : x ∈ enum l ↔ l[x.1]? = some x.2 :=
  mk_mem_enum_iff_getElem?

theorem fst_lt_of_mem_enum {x : Nat × α} {l : List α} (h : x ∈ enum l) : x.1 < length l := by
  simpa using fst_lt_add_of_mem_enumFrom h

theorem snd_mem_of_mem_enum {x : Nat × α} {l : List α} (h : x ∈ enum l) : x.2 ∈ l :=
  snd_mem_of_mem_enumFrom h

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

end List
