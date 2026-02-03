/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Graf, Paul Reichert
-/
module

prelude
public import Init.Data.Int.DivMod.Bootstrap
import Init.Data.Int.DivMod.Lemmas
import Init.Data.List.MinMax

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

protected theorem sum_pos_iff_exists_pos_nat {l : List Nat} : 0 < l.sum ↔ ∃ x ∈ l, 0 < x := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp [← ih]
    omega

@[deprecated List.sum_pos_iff_exists_pos_nat (since := "2025-01-15")]
protected def _root_.Nat.sum_pos_iff_exists_pos := @List.sum_pos_iff_exists_pos_nat

protected theorem sum_eq_zero_iff_forall_eq_nat {xs : List Nat} :
    xs.sum = 0 ↔ ∀ x ∈ xs, x = 0 := by
  rw [← Decidable.not_iff_not]
  simp [← Nat.pos_iff_ne_zero, List.sum_pos_iff_exists_pos_nat]

@[deprecated List.sum_pos_iff_exists_pos_nat (since := "2025-01-15")]
protected def _root_.Nat.sum_eq_zero_iff_forall_eq := @List.sum_eq_zero_iff_forall_eq_nat

@[simp]
theorem sum_replicate_nat {n : Nat} {a : Nat} : (replicate n a).sum = n * a := by
  induction n <;> simp_all [replicate_succ, Nat.add_mul, Nat.add_comm]

theorem sum_append_nat {l₁ l₂ : List Nat} : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  simp [sum_append]

theorem sum_reverse_nat (xs : List Nat) : xs.reverse.sum = xs.sum := by
  simp [sum_reverse]

theorem sum_eq_foldl_nat {xs : List Nat} : xs.sum = xs.foldl (init := 0) (· + ·) := by
  simp only [foldl_eq_foldr_reverse, Nat.add_comm, ← sum_eq_foldr, sum_reverse_nat]

theorem min_mul_length_le_sum_nat {xs : List Nat} (h : xs ≠ []) :
    xs.min h * xs.length ≤ xs.sum := by
  induction xs
  · contradiction
  · rename_i x xs ih
    cases xs
    · simp_all [List.min_singleton]
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, min_eq_get_min?,
      List.min?_cons (α := Nat), Option.get_some, length_cons,
      forall_const] at ih ⊢
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      apply Nat.add_le_add
      · apply Nat.min_le_left
      · refine Nat.le_trans ?_ ih
        rw [Nat.mul_le_mul_right_iff (by omega)]
        apply Nat.min_le_right

theorem mul_length_le_sum_of_min?_eq_some_nat {xs : List Nat} (h : xs.min? = some x) :
    x * xs.length ≤ xs.sum := by
  cases xs
  · simp_all
  · simp only [min?_eq_some_min (cons_ne_nil _ _), Option.some.injEq] at h
    simpa [← h] using min_mul_length_le_sum_nat _

theorem min_le_sum_div_length_nat {xs : List Nat} (h : xs ≠ []) :
    xs.min h ≤ xs.sum / xs.length := by
  have := min_mul_length_le_sum_nat h
  rwa [Nat.le_div_iff_mul_le]
  simp [List.length_pos_iff, h]

theorem le_sum_div_length_of_min?_eq_some_nat {xs : List Nat} (h : xs.min? = some x) :
    x ≤ xs.sum / xs.length := by
  cases xs
  · simp_all
  · simp only [min?_eq_some_min (cons_ne_nil _ _), Option.some.injEq] at h
    simpa [← h] using min_le_sum_div_length_nat _

theorem sum_le_max_mul_length_nat {xs : List Nat} (h : xs ≠ []) :
    xs.sum ≤ xs.max h * xs.length := by
  induction xs
  · contradiction
  · rename_i x xs ih
    cases xs
    · simp_all [List.max_singleton]
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, max_eq_get_max?,
      List.max?_cons (α := Nat), Option.get_some, length_cons,
      forall_const, Option.elim_some] at ih ⊢
      rw [Nat.mul_add, Nat.mul_one, Nat.add_comm]
      apply Nat.add_le_add
      · apply Nat.le_max_left
      · refine Nat.le_trans ih ?_
        rw [Nat.mul_le_mul_right_iff (by omega)]
        apply Nat.le_max_right

theorem sum_le_max_mul_length_of_max?_eq_some_nat {xs : List Nat} (h : xs.max? = some x) :
    xs.sum ≤ x * xs.length := by
  cases xs
  · simp_all
  · simp only [max?_eq_some_max (cons_ne_nil _ _), Option.some.injEq] at h
    simp only [← h]
    apply sum_le_max_mul_length_nat

theorem sum_div_length_le_max_nat {xs : List Nat} (h : xs ≠ []) :
    xs.sum / xs.length ≤ xs.max h := by
  have := sum_le_max_mul_length_nat h
  rw [Nat.div_le_iff_le_mul, Nat.add_sub_assoc]
  · exact Nat.le_trans this (Nat.le_add_right _ _)
  · simp [Nat.one_le_iff_ne_zero, h]
  · simp [← Nat.ne_zero_iff_zero_lt, h]

theorem sum_div_length_le_max_of_max?_eq_some_nat {xs : List Nat} (h : xs.max? = some x) :
    xs.sum / xs.length ≤ x := by
  cases xs
  · simp_all
  · simp only [max?_eq_some_max (cons_ne_nil _ _), Option.some.injEq] at h
    simpa only [← h] using sum_div_length_le_max_nat _

end List
