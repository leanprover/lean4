/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

prelude
import Init.Data.List.Count
import Init.Data.List.Find
import Init.Data.List.MinMax
import Init.Data.Nat.Lemmas

/-!
# Miscellaneous `List` lemmas, that require more `Nat` lemmas than are available in `Init.Data.List.Lemmas`.

In particular, `omega` is available here.
-/

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

open Nat

namespace List

/-! ### dropLast -/

@[grind _=_]
theorem tail_dropLast {l : List α} : tail (dropLast l) = dropLast (tail l) := by
  ext1
  simp only [getElem?_tail, getElem?_dropLast, length_tail]
  split <;> split
  · rfl
  · omega
  · omega
  · rfl

@[simp, grind _=_] theorem dropLast_reverse {l : List α} : l.reverse.dropLast = l.tail.reverse := by
  apply ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [getElem_dropLast, getElem_reverse, length_tail, getElem_tail]
    congr
    simp only [length_dropLast, length_reverse, length_tail] at h₁ h₂
    omega

/-! ### filter -/

@[simp]
theorem length_filter_pos_iff {l : List α} {p : α → Bool} :
    0 < (filter p l).length ↔ ∃ x ∈ l, p x := by
  simpa [length_eq_countP_add_countP, countP_eq_length_filter] using
    countP_pos_iff (p := p)

@[simp]
theorem length_filter_lt_length_iff_exists {l} :
    (filter p l).length < l.length ↔ ∃ x ∈ l, ¬p x := by
  simp [length_eq_countP_add_countP p (l := l), countP_eq_length_filter]

/-! ### filterMap -/

@[simp]
theorem length_filterMap_pos_iff {xs : List α} {f : α → Option β} :
    0 < (filterMap f xs).length ↔ ∃ (x : α) (_ : x ∈ xs) (b : β), f x = some b := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [filterMap, mem_cons, exists_prop, exists_eq_or_imp]
    split
    · simp_all [ih]
    · simp_all

@[simp]
theorem length_filterMap_lt_length_iff_exists {xs : List α} {f : α → Option β} :
    (filterMap f xs).length < xs.length ↔ ∃ (x : α) (_ : x ∈ xs), f x = none := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [filterMap, mem_cons, exists_prop, exists_eq_or_imp]
    split
    · simp_all only [exists_prop, length_cons, true_or, iff_true]
      have := length_filterMap_le f xs
      omega
    · simp_all

/-! ### reverse -/

theorem getElem_eq_getElem_reverse {l : List α} {i} (h : i < l.length) :
    l[i] = l.reverse[l.length - 1 - i]'(by simpa using Nat.sub_one_sub_lt_of_lt h) := by
  rw [getElem_reverse]
  congr
  omega

/-! ### leftpad -/

/-- The length of the List returned by `List.leftpad n a l` is equal
  to the larger of `n` and `l.length` -/
-- We don't mark this as a `@[simp]` lemma since we allow `simp` to unfold `leftpad`,
-- so the left hand side simplifies directly to `n - l.length + l.length`.
theorem length_leftpad {n : Nat} {a : α} {l : List α} :
    (leftpad n a l).length = max n l.length := by
  simp only [leftpad, length_append, length_replicate, Nat.sub_add_eq_max]

@[deprecated length_leftpad (since := "2025-02-24")]
abbrev leftpad_length := @length_leftpad

theorem length_rightpad {n : Nat} {a : α} {l : List α} :
    (rightpad n a l).length = max n l.length := by
  simp [rightpad]
  omega

/-! ### intersperse -/
section intersperse

variable {l : List α} {sep : α} {i : Nat}

@[simp, grind =] theorem length_intersperse : (l.intersperse sep).length = 2 * l.length - 1 := by
  fun_induction intersperse <;> simp only [intersperse, length_cons, length_nil] at *
  rename_i h _
  have := length_pos_iff.mpr h
  omega

@[simp] theorem getElem?_intersperse_two_mul : (l.intersperse sep)[2 * i]? = l[i]? := by
  induction l using intersperse.induct_unfolding sep generalizing i <;> cases i
  all_goals simp [mul_succ, *]

theorem getElem?_intersperse_two_mul_add_one (h : i + 1 < l.length) :
    (l.intersperse sep)[2 * i + 1]? = some sep := by
  fun_induction intersperse generalizing i
  · contradiction
  · contradiction
  · rename_i hn _
    have ⟨_, tl, _⟩ := ne_nil_iff_exists_cons.mp hn
    cases tl <;> cases i <;> simp_all +arith

@[grind =]
theorem getElem?_intersperse :
    (l.intersperse sep)[i]? =
      if i % 2 = 0 then
        l[i / 2]?
      else
        if i < 2 * l.length - 1 then some sep else none := by
  split
  · have p : i = 2 * (i / 2) := by omega
    conv => lhs; rw [p]
    rw [getElem?_intersperse_two_mul]
  · split
    · have p : i = 2 * (i / 2) + 1 := by omega
      conv => lhs; rw [p]
      rw [getElem?_intersperse_two_mul_add_one]
      omega
    · rw [getElem?_eq_none_iff]
      simp
      omega

@[simp] theorem getElem_intersperse_two_mul (h : 2 * i < (l.intersperse sep).length) :
    (l.intersperse sep)[2 * i] = l[i]'(by rw [length_intersperse] at h; omega) := by
  rw [← Option.some_inj, ← getElem?_eq_getElem h]
  simp

@[simp] theorem getElem_intersperse_two_mul_add_one (h : 2 * i + 1 < (l.intersperse sep).length) :
    (l.intersperse sep)[2 * i + 1] = sep := by
  rw [← Option.some_inj, ← getElem?_eq_getElem h, getElem?_intersperse_two_mul_add_one]
  rw [length_intersperse] at h
  omega

@[grind =]
theorem getElem_intersperse (h) :
    (l.intersperse sep)[i] =
      if i % 2 = 0 then l[i / 2]'(by simp at h; omega) else sep := by
  split
  · have p : i = 2 * (i / 2) := by omega
    conv => lhs; simp +singlePass only [p]
    rw [getElem_intersperse_two_mul]
  · have p : i = 2 * (i / 2) + 1 := by omega
    conv => lhs; simp +singlePass only [p]
    rw [getElem_intersperse_two_mul_add_one]

theorem getElem_eq_getElem_intersperse_two_mul (h : i < l.length) :
    l[i] = (l.intersperse sep)[2 * i]'(by rw [length_intersperse]; omega) := by
  simp

end intersperse

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
    simp [mem_eraseIdx_iff_getElem, @eq_comm _ a, succ_inj, Nat.succ_lt_succ_iff]

theorem mem_eraseIdx_iff_getElem? {x : α} {l} {k} : x ∈ eraseIdx l k ↔ ∃ i ≠ k, l[i]? = some x := by
  simp only [mem_eraseIdx_iff_getElem, getElem_eq_iff, exists_and_left]
  refine exists_congr fun i => and_congr_right' ?_
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro h;
    obtain ⟨h', -⟩ := getElem?_eq_some_iff.1 h
    exact ⟨h', h⟩

/-! ### min? -/

-- A specialization of `min?_eq_some_iff` to Nat.
theorem min?_eq_some_iff' {xs : List Nat} :
    xs.min? = some a ↔ (a ∈ xs ∧ ∀ b ∈ xs, a ≤ b) :=
  min?_eq_some_iff
    (le_refl := Nat.le_refl)
    (min_eq_or := fun _ _ => Nat.min_def .. ▸ by split <;> simp)
    (le_min_iff := fun _ _ _ => Nat.le_min)

theorem min?_get_le_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) :
    l.min?.get (isSome_min?_of_mem h) ≤ a := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    simp only [min?_cons, Option.get_some] at ih ⊢
    rcases mem_cons.1 h with (rfl|h)
    · cases t.min? with
      | none => simp
      | some b => simpa using Nat.min_le_left _ _
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (isSome_min?_of_mem h)
      simp only [hq, Option.elim_some] at ih ⊢
      exact Nat.le_trans (Nat.min_le_right _ _) (ih h)

theorem min?_getD_le_of_mem {l : List Nat} {a k : Nat} (h : a ∈ l) : l.min?.getD k ≤ a :=
  Option.get_eq_getD _ ▸ min?_get_le_of_mem h

/-! ### max? -/

-- A specialization of `max?_eq_some_iff` to Nat.
theorem max?_eq_some_iff' {xs : List Nat} :
    xs.max? = some a ↔ (a ∈ xs ∧ ∀ b ∈ xs, b ≤ a) :=
  max?_eq_some_iff
    (le_refl := Nat.le_refl)
    (max_eq_or := fun _ _ => Nat.max_def .. ▸ by split <;> simp)
    (max_le_iff := fun _ _ _ => Nat.max_le)

theorem le_max?_get_of_mem {l : List Nat} {a : Nat} (h : a ∈ l) :
    a ≤ l.max?.get (isSome_max?_of_mem h) := by
  induction l with
  | nil => simp at h
  | cons b t ih =>
    simp only [max?_cons, Option.get_some] at ih ⊢
    rcases mem_cons.1 h with (rfl|h)
    · cases t.max? with
      | none => simp
      | some b => simpa using Nat.le_max_left _ _
    · obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 (isSome_max?_of_mem h)
      simp only [hq, Option.elim_some] at ih ⊢
      exact Nat.le_trans (ih h) (Nat.le_max_right _ _)

theorem le_max?_getD_of_mem {l : List Nat} {a k : Nat} (h : a ∈ l) :
    a ≤ l.max?.getD k :=
  Option.get_eq_getD _ ▸ le_max?_get_of_mem h

end List
