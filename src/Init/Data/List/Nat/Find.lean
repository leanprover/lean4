/-
Copyright (c) 2024 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.List.Nat.Range
import Init.Data.List.Find

namespace List

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
