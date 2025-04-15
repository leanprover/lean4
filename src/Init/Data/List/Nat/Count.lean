/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Count
import Init.Data.Nat.Lemmas

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

open Nat

theorem countP_set {p : α → Bool} {l : List α} {i : Nat} {a : α} (h : i < l.length) :
    (l.set i a).countP p = l.countP p - (if p l[i] then 1 else 0) + (if p a then 1 else 0) := by
  induction l generalizing i with
  | nil => simp at h
  | cons x l ih =>
    cases i with
    | zero => simp [countP_cons]
    | succ i =>
      simp [add_one_lt_add_one_iff] at h
      simp [countP_cons, ih h]
      have : (if p l[i] = true then 1 else 0) ≤ l.countP p := boole_getElem_le_countP (p := p) h
      omega

theorem count_set [BEq α] {a b : α} {l : List α} {i : Nat} (h : i < l.length) :
    (l.set i a).count b = l.count b - (if l[i] == b then 1 else 0) + (if a == b then 1 else 0) := by
  simp [count_eq_countP, countP_set, h]

theorem countP_replace [BEq α] [LawfulBEq α] {a b : α} {l : List α} {p : α → Bool} :
    (l.replace a b).countP p =
      if l.contains a then l.countP p + (if p b then 1 else 0) - (if p a then 1 else 0) else l.countP p := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp [replace_cons]
    split <;> rename_i h
    · simp at h
      simp [h, ih, countP_cons]
      omega
    · simp only [beq_eq_false_iff_ne, ne_eq] at h
      simp only [countP_cons, ih, contains_eq_mem, decide_eq_true_eq, mem_cons, h, false_or]
      split <;> rename_i h'
      · by_cases h'' : p a
        · have : countP p l > 0 := countP_pos_iff.mpr ⟨a, h', h''⟩
          simp [h'']
          omega
        · simp [h'']
          omega
      · omega

theorem count_replace [BEq α] [LawfulBEq α] {a b c : α} {l : List α} :
    (l.replace a b).count c =
      if l.contains a then l.count c + (if b == c then 1 else 0) - (if a == c then 1 else 0) else l.count c := by
  simp [count_eq_countP, countP_replace]

/--
The number of elements satisfying a predicate in a sublist is at least the number of elements satisfying the predicate in the list,
minus the difference in the lengths.
-/
theorem Sublist.le_countP (s : l₁ <+ l₂) (p) : countP p l₂ - (l₂.length - l₁.length) ≤ countP p l₁ := by
  match s with
  | .slnil => simp
  | .cons a s =>
    rename_i l
    simp only [countP_cons, length_cons]
    have := s.le_countP p
    have := s.length_le
    split <;> omega
  | .cons₂ a s =>
    rename_i l₁ l₂
    simp only [countP_cons, length_cons]
    have := s.le_countP p
    have := s.length_le
    split <;> omega

theorem IsPrefix.le_countP (s : l₁ <+: l₂) : countP p l₂ - (l₂.length - l₁.length) ≤ countP p l₁ :=
  s.sublist.le_countP _

theorem IsSuffix.le_countP (s : l₁ <:+ l₂) : countP p l₂ - (l₂.length - l₁.length) ≤ countP p l₁ :=
  s.sublist.le_countP _

theorem IsInfix.le_countP (s : l₁ <:+: l₂) : countP p l₂ - (l₂.length - l₁.length) ≤ countP p l₁ :=
  s.sublist.le_countP _

/--
The number of elements satisfying a predicate in the tail of a list is
at least one less than the number of elements satisfying the predicate in the list.
-/
theorem le_countP_tail {l} : countP p l - 1 ≤ countP p l.tail := by
  have := (tail_sublist l).le_countP p
  simp only [length_tail] at this
  omega

variable [BEq α]

theorem Sublist.le_count (s : l₁ <+ l₂) (a : α) : count a l₂ - (l₂.length - l₁.length) ≤ count a l₁ :=
  s.le_countP _

theorem IsPrefix.le_count (s : l₁ <+: l₂) (a : α) : count a l₂ - (l₂.length - l₁.length) ≤ count a l₁ :=
  s.sublist.le_count _

theorem IsSuffix.le_count (s : l₁ <:+ l₂) (a : α) : count a l₂ - (l₂.length - l₁.length) ≤ count a l₁ :=
  s.sublist.le_count _

theorem IsInfix.le_count (s : l₁ <:+: l₂) (a : α) : count a l₂ - (l₂.length - l₁.length) ≤ count a l₁ :=
  s.sublist.le_count _

theorem le_count_tail {a : α} {l : List α} : count a l - 1 ≤ count a l.tail :=
  le_countP_tail

end List
