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

theorem length_filter_lt_length_iff_exists (l) :
    length (filter p l) < length l ↔ ∃ x ∈ l, ¬p x := by
  simpa [length_eq_countP_add_countP p l, countP_eq_length_filter] using
  countP_pos (fun x => ¬p x) (l := l)

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
