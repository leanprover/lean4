/-
Copyright (c) 2024 Lean FRO All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Nat.Lemmas
import Init.Data.List.Basic

namespace List

/-! ### isEqv -/

theorem isEqv_eq_decide (a b : List α) (r) :
    isEqv a b r = if h : a.length = b.length then
      decide (∀ (i : Nat) (h' : i < a.length), r (a[i]'(h ▸ h')) (b[i]'(h ▸ h'))) else false := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp
  | cons a as ih =>
    cases b with
    | nil => simp
    | cons b bs =>
      simp only [isEqv, ih, length_cons, Nat.add_right_cancel_iff]
      split <;> simp [Nat.forall_lt_succ_left']

/-! ### beq -/

theorem beq_eq_isEqv [BEq α] (a b : List α) : a.beq b = isEqv a b (· == ·) := by
  induction a generalizing b with
  | nil =>
    cases b <;> simp
  | cons a as ih =>
    cases b with
    | nil => simp
    | cons b bs =>
      simp only [beq_cons₂, ih, isEqv_eq_decide, length_cons, Nat.add_right_cancel_iff,
        Nat.forall_lt_succ_left', getElem_cons_zero, getElem_cons_succ, Bool.decide_and,
        Bool.decide_eq_true]
      split <;> simp

theorem beq_eq_decide [BEq α] (a b : List α) :
    (a == b) = if h : a.length = b.length then
      decide (∀ (i : Nat) (h' : i < a.length), a[i] == b[i]'(h ▸ h')) else false := by
  simp [BEq.beq, beq_eq_isEqv, isEqv_eq_decide]

end List
