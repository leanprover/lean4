/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Graf, Paul Reichert
-/
module

prelude
import Init.Data.Int.DivMod.Lemmas
import Init.Data.List.MinMax
public import Init.Data.Int.DivMod.Basic
public import Init.Data.List.Basic
import Init.Omega

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

@[simp]
theorem sum_replicate_int {n : Nat} {a : Int} : (replicate n a).sum = n * a := by
  induction n <;> simp_all [replicate_succ, Int.add_mul, Int.add_comm]

theorem sum_append_int {l₁ l₂ : List Int} : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  simp [sum_append]

theorem sum_reverse_int (xs : List Int) : xs.reverse.sum = xs.sum := by
  simp [sum_reverse]

theorem min_mul_length_le_sum_int {xs : List Int} (h : xs ≠ []) :
    xs.min h * xs.length ≤ xs.sum := by
  induction xs
  · contradiction
  · rename_i x xs ih
    cases xs
    · simp_all [List.min_singleton]
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, min_eq_get_min?,
      List.min?_cons (α := Int), Option.get_some, length_cons, Int.natCast_add, Int.cast_ofNat_Int,
      forall_const] at ih ⊢
      rw [Int.mul_add, Int.mul_one, Int.add_comm]
      apply Int.add_le_add
      · apply Int.min_le_left
      · refine Int.le_trans ?_ ih
        rw [Int.mul_le_mul_right (by omega)]
        apply Int.min_le_right

theorem mul_length_le_sum_of_min?_eq_some_int {xs : List Int} (h : xs.min? = some x) :
    x * xs.length ≤ xs.sum := by
  cases xs
  · simp_all
  · simp only [min?_eq_some_min (cons_ne_nil _ _), Option.some.injEq] at h
    simpa [← h] using min_mul_length_le_sum_int _

theorem min_le_sum_div_length_int {xs : List Int} (h : xs ≠ []) :
    xs.min h ≤ xs.sum / xs.length := by
  have := min_mul_length_le_sum_int h
  rwa [Int.le_ediv_iff_mul_le]
  simp [List.length_pos_iff, h]

theorem le_sum_div_length_of_min?_eq_some_int {xs : List Int} (h : xs.min? = some x) :
    x ≤ xs.sum / xs.length := by
  cases xs
  · simp_all
  · simp only [min?_eq_some_min (cons_ne_nil _ _), Option.some.injEq] at h
    simpa [← h] using min_le_sum_div_length_int _

theorem sum_le_max_mul_length_int {xs : List Int} (h : xs ≠ []) :
    xs.sum ≤ xs.max h * xs.length := by
  induction xs
  · contradiction
  · rename_i x xs ih
    cases xs
    · simp_all [List.max_singleton]
    · simp only [ne_eq, reduceCtorEq, not_false_eq_true, max_eq_get_max?,
      List.max?_cons (α := Int), Option.get_some, length_cons, Int.natCast_add, Int.cast_ofNat_Int,
      forall_const] at ih ⊢
      rw [Int.mul_add, Int.mul_one, Int.add_comm]
      apply Int.add_le_add
      · apply Int.le_max_left
      · refine Int.le_trans ih ?_
        rw [Int.mul_le_mul_right (by omega)]
        apply Int.le_max_right

theorem sum_le_max_mul_length_of_max?_eq_some_int {xs : List Int} (h : xs.max? = some x) :
    xs.sum ≤ x * xs.length := by
  cases xs
  · simp_all
  · simp only [max?_eq_some_max (cons_ne_nil _ _), Option.some.injEq] at h
    simpa [← h] using sum_le_max_mul_length_int _

theorem sum_div_length_le_max_int {xs : List Int} (h : xs ≠ []) :
    xs.sum / xs.length ≤ xs.max h := by
  have := sum_le_max_mul_length_int h
  rw [Int.ediv_le_iff_le_mul]
  · refine Int.lt_of_le_of_lt this ?_
    apply Int.lt_add_of_pos_right
    simp [← Nat.ne_zero_iff_zero_lt, h]
  · simp [List.length_pos_iff, h]

theorem sum_div_length_le_max_of_max?_eq_some_int {xs : List Int} (h : xs.max? = some x) :
    xs.sum / xs.length ≤ x := by
  cases xs
  · simp_all
  · simp only [max?_eq_some_max (cons_ne_nil _ _), Option.some.injEq] at h
    simpa [← h] using sum_div_length_le_max_int _

end List
