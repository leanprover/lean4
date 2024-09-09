/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
prelude
import Init.Data.List.Count
import Init.Data.List.MinMax
import Init.Data.Nat.Lemmas

/-!
# Miscellaneous `List` lemmas, that require more `Nat` lemmas than are available in `Init.Data.List.Lemmas`.

In particular, `omega` is available here.
-/

open Nat

namespace List

/-! ### filter -/

theorem length_filter_lt_length_iff_exists {l} :
    length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x := by
  simpa [length_eq_countP_add_countP p l, countP_eq_length_filter] using
    countP_pos_iff (p := fun x => ¬p x)

/-! ### reverse -/

theorem getElem_eq_getElem_reverse {l : List α} {i} (h : i < l.length) :
    l[i] = l.reverse[l.length - 1 - i]'(by simpa using Nat.sub_one_sub_lt_of_lt h) := by
  rw [getElem_reverse]
  congr
  omega

/-! ### leftpad -/

/-- The length of the List returned by `List.leftpad n a l` is equal
  to the larger of `n` and `l.length` -/
@[simp]
theorem leftpad_length (n : Nat) (a : α) (l : List α) :
    (leftpad n a l).length = max n l.length := by
  simp only [leftpad, length_append, length_replicate, Nat.sub_add_eq_max]

/-! ### eraseIdx -/

theorem mem_eraseIdx_iff_getElem {x : α} :
    ∀ {l} {k}, x ∈ eraseIdx l k ↔ ∃ i h, i ≠ k ∧ l[i]'h = x
  | [], _ => by
    simp only [eraseIdx, not_mem_nil, false_iff]
    rintro ⟨i, h, -⟩
    exact Nat.not_lt_zero _ h
  | a::l, 0 => by simp [mem_iff_getElem, Nat.succ_lt_succ_iff]
  | a::l, k+1 => by
    rw [← Nat.or_exists_add_one]
    simp [mem_eraseIdx_iff_getElem, @eq_comm _ a, succ_inj', Nat.succ_lt_succ_iff]

theorem mem_eraseIdx_iff_getElem? {x : α} {l} {k} : x ∈ eraseIdx l k ↔ ∃ i ≠ k, l[i]? = some x := by
  simp only [mem_eraseIdx_iff_getElem, getElem_eq_iff, exists_and_left]
  refine exists_congr fun i => and_congr_right' ?_
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro h;
    obtain ⟨h', -⟩ := getElem?_eq_some_iff.1 h
    exact ⟨h', h⟩

/-! ### minimum? -/

-- A specialization of `minimum?_eq_some_iff` to Nat.
theorem minimum?_eq_some_iff' {xs : List Nat} :
    xs.minimum? = some a ↔ (a ∈ xs ∧ ∀ b ∈ xs, a ≤ b) :=
  minimum?_eq_some_iff
    (le_refl := Nat.le_refl)
    (min_eq_or := fun _ _ => by omega)
    (le_min_iff := fun _ _ _ => by omega)

-- This could be generalized,
-- but will first require further work on order typeclasses in the core repository.
theorem minimum?_cons' {a : Nat} {l : List Nat} :
    (a :: l).minimum? = some (match l.minimum? with
    | none => a
    | some m => min a m) := by
  rw [minimum?_eq_some_iff']
  split <;> rename_i h m
  · simp_all
  · rw [minimum?_eq_some_iff'] at m
    obtain ⟨m, le⟩ := m
    rw [Nat.min_def]
    constructor
    · split
      · exact mem_cons_self a l
      · exact mem_cons_of_mem a m
    · intro b m
      cases List.mem_cons.1 m with
      | inl => split <;> omega
      | inr h =>
        specialize le b h
        split <;> omega

/-! ### maximum? -/

-- A specialization of `maximum?_eq_some_iff` to Nat.
theorem maximum?_eq_some_iff' {xs : List Nat} :
    xs.maximum? = some a ↔ (a ∈ xs ∧ ∀ b ∈ xs, b ≤ a) :=
  maximum?_eq_some_iff
    (le_refl := Nat.le_refl)
    (max_eq_or := fun _ _ => by omega)
    (max_le_iff := fun _ _ _ => by omega)

-- This could be generalized,
-- but will first require further work on order typeclasses in the core repository.
theorem maximum?_cons' {a : Nat} {l : List Nat} :
    (a :: l).maximum? = some (match l.maximum? with
    | none => a
    | some m => max a m) := by
  rw [maximum?_eq_some_iff']
  split <;> rename_i h m
  · simp_all
  · rw [maximum?_eq_some_iff'] at m
    obtain ⟨m, le⟩ := m
    rw [Nat.max_def]
    constructor
    · split
      · exact mem_cons_of_mem a m
      · exact mem_cons_self a l
    · intro b m
      cases List.mem_cons.1 m with
      | inl => split <;> omega
      | inr h =>
        specialize le b h
        split <;> omega

end List
