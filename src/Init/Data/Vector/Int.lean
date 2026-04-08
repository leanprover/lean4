/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Graf, Paul Reichert
-/
module

prelude
public import Init.Data.Vector.Basic
import Init.Data.Array.Int
import Init.Data.Int.Lemmas
import Init.Data.Vector.Lemmas

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

@[simp] theorem sum_replicate_int {n : Nat} {a : Int} : (replicate n a).sum = n * a := by
  simp [← sum_toArray, Array.sum_replicate_int]

theorem sum_append_int {as₁ as₂ : Vector Int n} : (as₁ ++ as₂).sum = as₁.sum + as₂.sum := by
  simp [← sum_toArray]

theorem sum_reverse_int (xs : Vector Int n) : xs.reverse.sum = xs.sum := by
  simp [sum_reverse]

theorem sum_eq_foldl_int {xs : Vector Int n} : xs.sum = xs.foldl (b := 0) (· + ·) := by
  simp only [foldl_eq_foldr_reverse, Int.add_comm, ← sum_eq_foldr, sum_reverse_int]

@[simp] theorem prod_replicate_int {n : Nat} {a : Int} : (replicate n a).prod = a ^ n := by
  simp [← prod_toArray, Array.prod_replicate_int]

theorem prod_append_int {as₁ as₂ : Vector Int n} : (as₁ ++ as₂).prod = as₁.prod * as₂.prod := by
  simp [← prod_toArray]

theorem prod_reverse_int (xs : Vector Int n) : xs.reverse.prod = xs.prod := by
  simp [prod_reverse]

theorem prod_eq_foldl_int {xs : Vector Int n} : xs.prod = xs.foldl (b := 1) (· * ·) := by
  simp only [foldl_eq_foldr_reverse, Int.mul_comm, ← prod_eq_foldr, prod_reverse_int]

end Vector
