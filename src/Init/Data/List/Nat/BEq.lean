/-
Copyright (c) 2024 Lean FRO All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Data.Nat.Lemmas
import Init.Data.List.Basic

-- set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
-- set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

/-! ### isEqv -/

theorem isEqv_eq_decide (as bs : List α) (r) :
    isEqv as bs r = if h : as.length = bs.length then
      decide (∀ (i : Nat) (h' : i < as.length), r (as[i]'(h ▸ h')) (bs[i]'(h ▸ h'))) else false := by
  induction as generalizing bs with
  | nil =>
    cases bs <;> simp
  | cons a as ih =>
    cases bs with
    | nil => simp
    | cons b bs =>
      simp only [isEqv, ih, length_cons, Nat.add_right_cancel_iff]
      split <;> simp [Nat.forall_lt_succ_left']

/-! ### beq -/

theorem beq_eq_isEqv [BEq α] (as bs : List α) : as.beq bs = isEqv as bs (· == ·) := by
  induction as generalizing bs with
  | nil =>
    cases bs <;> simp
  | cons a as ih =>
    cases bs with
    | nil => simp
    | cons b bs =>
      simp only [beq_cons₂, ih, isEqv_eq_decide, length_cons, Nat.add_right_cancel_iff,
        Nat.forall_lt_succ_left', getElem_cons_zero, getElem_cons_succ, Bool.decide_and,
        Bool.decide_eq_true]
      split <;> simp

theorem beq_eq_decide [BEq α] (as bs : List α) :
    (as == bs) = if h : as.length = bs.length then
      decide (∀ (i : Nat) (h' : i < as.length), as[i] == bs[i]'(h ▸ h')) else false := by
  simp [BEq.beq, beq_eq_isEqv, isEqv_eq_decide]

end List
