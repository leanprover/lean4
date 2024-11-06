/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Nat.Range
import Init.Data.List.Find

namespace List

open Nat

theorem find?_eq_some_iff_getElem {xs : List α} {p : α → Bool} {b : α} :
    xs.find? p = some b ↔ p b ∧ ∃ i h, xs[i] = b ∧ ∀ j : Nat, (hj : j < i) → !p xs[j] := by
  rw [find?_eq_some_iff_append]
  simp only [Bool.not_eq_eq_eq_not, Bool.not_true, exists_and_right, and_congr_right_iff]
  intro w
  constructor
  · rintro ⟨as, ⟨bs, rfl⟩, h⟩
    refine ⟨as.length, ⟨?_, ?_, ?_⟩⟩
    · simp only [length_append, length_cons]
      refine Nat.lt_add_of_pos_right (zero_lt_succ bs.length)
    · rw [getElem_append_right (Nat.le_refl as.length)]
      simp
    · intro j h'
      rw [getElem_append_left h']
      exact h _ (getElem_mem h')
  · rintro ⟨i, h, rfl, h'⟩
    refine ⟨xs.take i, ⟨xs.drop (i+1), ?_⟩, ?_⟩
    · rw [getElem_cons_drop, take_append_drop]
    · intro a m
      rw [mem_take_iff_getElem] at m
      obtain ⟨j, h, rfl⟩ := m
      apply h'
      omega

theorem findIdx?_eq_some_le_of_findIdx?_eq_some {xs : List α} {p q : α → Bool} (w : ∀ x ∈ xs, p x → q x) {i : Nat}
    (h : xs.findIdx? p = some i) : ∃ j, j ≤ i ∧ xs.findIdx? q = some j := by
  simp only [findIdx?_eq_findSome?_enum] at h
  rw [findSome?_eq_some_iff] at h
  simp only [Option.ite_none_right_eq_some, Option.some.injEq, ite_eq_right_iff, reduceCtorEq,
    imp_false, Bool.not_eq_true, Prod.forall, exists_and_right, Prod.exists] at h
  obtain ⟨h, h₁, b, ⟨es, h₂⟩, ⟨hb, rfl⟩, h₃⟩ := h
  rw [enum_eq_enumFrom, enumFrom_eq_append_iff] at h₂
  obtain ⟨l₁', l₂', rfl, rfl, h₂⟩ := h₂
  rw [eq_comm, enumFrom_eq_cons_iff] at h₂
  obtain ⟨a, as, rfl, h₂, rfl⟩ := h₂
  simp only [Nat.zero_add, Prod.mk.injEq] at h₂
  obtain ⟨rfl, rfl⟩ := h₂
  simp only [findIdx?_append]
  match h : findIdx? q l₁' with
  | some j =>
    refine ⟨j, ?_, by simp⟩
    rw [findIdx?_eq_some_iff_findIdx_eq] at h
    omega
  | none =>
    refine ⟨l₁'.length, by simp, by simp_all⟩
