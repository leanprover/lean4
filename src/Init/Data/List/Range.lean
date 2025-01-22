/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Pairwise
import Init.Data.List.Zip

/-!
# Lemmas about `List.range` and `List.enum`

Most of the results are deferred to `Data.Init.List.Nat.Range`, where more results about
natural arithmetic are available.
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

theorem range'_ne_nil (s : Nat) {n : Nat} : range' s n ≠ [] ↔ n ≠ 0 := by
  cases n <;> simp

@[simp] theorem range'_zero : range' s 0 step = [] := by
  simp

@[simp] theorem range'_one {s step : Nat} : range' s 1 step = [s] := rfl

@[simp] theorem tail_range' (n : Nat) : (range' s n step).tail = range' (s + step) (n - 1) step := by
  cases n with
  | zero => simp
  | succ n => simp [range'_succ]

@[simp] theorem range'_inj : range' s n = range' s' n' ↔ n = n' ∧ (n = 0 ∨ s = s') := by
  constructor
  · intro h
    have h' := congrArg List.length h
    simp at h'
    subst h'
    cases n with
    | zero => simp
    | succ n =>
      simp only [range'_succ] at h
      simp_all
  · rintro ⟨rfl, rfl | rfl⟩ <;> simp

theorem mem_range' : ∀{n}, m ∈ range' s n step ↔ ∃ i < n, m = s + step * i
  | 0 => by simp [range', Nat.not_lt_zero]
  | n + 1 => by
    have h (i) : i ≤ n ↔ i = 0 ∨ ∃ j, i = succ j ∧ j < n := by
      cases i <;> simp [Nat.succ_le, Nat.succ_inj']
    simp [range', mem_range', Nat.lt_succ, h]; simp only [← exists_and_right, and_assoc]
    rw [exists_comm]; simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

theorem getElem?_range' (s step) :
    ∀ {m n : Nat}, m < n → (range' s n step)[m]? = some (s + step * m)
  | 0, n + 1, _ => by simp [range'_succ]
  | m + 1, n + 1, h => by
    simp only [range'_succ, getElem?_cons_succ]
    exact (getElem?_range' (s + step) step (by exact succ_lt_succ_iff.mp h)).trans <| by
      simp [Nat.mul_succ, Nat.add_assoc, Nat.add_comm]

@[simp] theorem getElem_range' {n m step} (i) (H : i < (range' n m step).length) :
    (range' n m step)[i] = n + step * i :=
  (getElem?_eq_some_iff.1 <| getElem?_range' n step (by simpa using H)).2

theorem head?_range' (n : Nat) : (range' s n).head? = if n = 0 then none else some s := by
  induction n <;> simp_all [range'_succ, head?_append]

@[simp] theorem head_range' (n : Nat) (h) : (range' s n).head h = s := by
  repeat simp_all [head?_range', head_eq_iff_head?_eq_some]

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

theorem range_loop_range' : ∀ s n : Nat, range.loop s (range' s n) = range' 0 (n + s)
  | 0, _ => rfl
  | s + 1, n => by rw [← Nat.add_assoc, Nat.add_right_comm n s 1]; exact range_loop_range' s (n + 1)

theorem range_eq_range' (n : Nat) : range n = range' 0 n :=
  (range_loop_range' n 0).trans <| by rw [Nat.zero_add]

theorem getElem?_range {m n : Nat} (h : m < n) : (range n)[m]? = some m := by
  simp [range_eq_range', getElem?_range' _ _ h]

@[simp] theorem getElem_range {n : Nat} (m) (h : m < (range n).length) : (range n)[m] = m := by
  simp [range_eq_range']

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

/-! ### enumFrom -/

@[simp]
theorem enumFrom_eq_nil {n : Nat} {l : List α} : List.enumFrom n l = [] ↔ l = [] := by
  cases l <;> simp

@[simp] theorem enumFrom_length : ∀ {n} {l : List α}, (enumFrom n l).length = l.length
  | _, [] => rfl
  | _, _ :: _ => congrArg Nat.succ enumFrom_length

@[simp]
theorem getElem?_enumFrom :
    ∀ n (l : List α) m, (enumFrom n l)[m]? = l[m]?.map fun a => (n + m, a)
  | _, [], _ => rfl
  | _, _ :: _, 0 => by simp
  | n, _ :: l, m + 1 => by
    simp only [enumFrom_cons, getElem?_cons_succ]
    exact (getElem?_enumFrom (n + 1) l m).trans <| by rw [Nat.add_right_comm]; rfl

@[simp]
theorem getElem_enumFrom (l : List α) (n) (i : Nat) (h : i < (l.enumFrom n).length) :
    (l.enumFrom n)[i] = (n + i, l[i]'(by simpa [enumFrom_length] using h)) := by
  simp only [enumFrom_length] at h
  rw [getElem_eq_getElem?_get]
  simp only [getElem?_enumFrom, getElem?_eq_getElem h]
  simp

@[simp]
theorem tail_enumFrom (l : List α) (n : Nat) : (enumFrom n l).tail = enumFrom (n + 1) l.tail := by
  induction l generalizing n with
  | nil => simp
  | cons _ l ih => simp [ih, enumFrom_cons]

theorem map_fst_add_enumFrom_eq_enumFrom (l : List α) (n k : Nat) :
    map (Prod.map (· + n) id) (enumFrom k l) = enumFrom (n + k) l :=
  ext_getElem? fun i ↦ by simp [(· ∘ ·), Nat.add_comm, Nat.add_left_comm]; rfl

theorem map_fst_add_enum_eq_enumFrom (l : List α) (n : Nat) :
    map (Prod.map (· + n) id) (enum l) = enumFrom n l :=
  map_fst_add_enumFrom_eq_enumFrom l _ _

theorem enumFrom_cons' (n : Nat) (x : α) (xs : List α) :
    enumFrom n (x :: xs) = (n, x) :: (enumFrom n xs).map (Prod.map (· + 1) id) := by
  rw [enumFrom_cons, Nat.add_comm, ← map_fst_add_enumFrom_eq_enumFrom]

@[simp]
theorem enumFrom_map_fst (n) :
    ∀ (l : List α), map Prod.fst (enumFrom n l) = range' n l.length
  | [] => rfl
  | _ :: _ => congrArg (cons _) (enumFrom_map_fst _ _)

@[simp]
theorem enumFrom_map_snd : ∀ (n) (l : List α), map Prod.snd (enumFrom n l) = l
  | _, [] => rfl
  | _, _ :: _ => congrArg (cons _) (enumFrom_map_snd _ _)

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

theorem enum_eq_enumFrom {l : List α} : l.enum = l.enumFrom 0 := rfl

theorem enumFrom_eq_map_enum (l : List α) (n : Nat) :
    enumFrom n l = (enum l).map (Prod.map (· + n) id) := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    simp only [enumFrom_cons, ih, enum_cons, map_cons, Prod.map_apply, Nat.zero_add, id_eq, map_map,
      cons.injEq, map_inj_left, Function.comp_apply, Prod.forall, Prod.mk.injEq, and_true, true_and]
    intro a b _
    exact (succ_add a n).symm

end List
