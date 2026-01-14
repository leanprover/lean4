/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Paul Reichert
-/
module

prelude
public import Init.Data.Int.DivMod.Bootstrap
import Init.Data.Int.Lemmas
import Init.Data.Int.LemmasAux
import Init.Data.Int.DivMod.Lemmas
import Init.Data.List.Lemmas
import Init.Data.List.MinMax
import Init.Data.Int.Order
import Init.Data.Order.Lemmas

public section

namespace List

@[simp, grind =]
theorem sum_append_int {l₁ l₂ : List Int} : (l₁ ++ l₂).sum = l₁.sum + l₂.sum := by
  simp [sum_append]

@[simp, grind =]
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

end List
