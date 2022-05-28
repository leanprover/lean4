/-
Copyright (c) 2022 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Data.Array.Basic
import Init.Data.Nat.Linear
import Init.NotationExtra

theorem Array.of_push_eq_push {as bs : Array α} (h : as.push a = bs.push b) : as = bs ∧ a = b := by
  simp [push] at h
  have ⟨h₁, h₂⟩ := List.of_concat_eq_concat h
  cases as; cases bs
  simp_all

private theorem List.size_toArrayAux (as : List α) (bs : Array α) : (as.toArrayAux bs).size = as.length + bs.size := by
  induction as generalizing bs with
  | nil => simp [toArrayAux]
  | cons a as ih => simp_arith [toArrayAux, *]

private theorem List.of_toArrayAux_eq_toArrayAux {as bs : List α} {cs ds : Array α} (h : as.toArrayAux cs = bs.toArrayAux ds) (hlen : cs.size = ds.size) : as = bs ∧ cs = ds := by
  match as, bs with
  | [], []    => simp [toArrayAux] at h; simp [h]
  | a::as, [] => simp [toArrayAux] at h; rw [← h] at hlen; simp_arith [size_toArrayAux] at hlen
  | [], b::bs => simp [toArrayAux] at h; rw [h] at hlen; simp_arith [size_toArrayAux] at hlen
  | a::as, b::bs =>
    simp [toArrayAux] at h
    have : (cs.push a).size = (ds.push b).size := by simp [*]
    have ⟨ih₁, ih₂⟩ := of_toArrayAux_eq_toArrayAux h this
    simp [ih₁]
    have := Array.of_push_eq_push ih₂
    simp [this]

@[simp] theorem List.toArray_eq_toArray_eq (as bs : List α) : (as.toArray = bs.toArray) = (as = bs) := by
  apply propext; apply Iff.intro
  · intro h; simp [toArray] at h; have := of_toArrayAux_eq_toArrayAux h rfl; exact this.1
  · intro h; rw [h]
