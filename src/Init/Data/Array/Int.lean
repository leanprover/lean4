/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Graf, Paul Reichert
-/
module

prelude
public import Init.Data.Array.Basic
import Init.Data.Array.Lemmas
import Init.Data.Int.Lemmas
import Init.Data.List.Int.Sum

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

@[simp] theorem sum_replicate_int {n : Nat} {a : Int} : (replicate n a).sum = n * a := by
  rw [← List.toArray_replicate, List.sum_toArray]
  simp

theorem sum_append_int {as₁ as₂ : Array Int} : (as₁ ++ as₂).sum = as₁.sum + as₂.sum := by
  simp [sum_append]

theorem sum_reverse_int (xs : Array Int) : xs.reverse.sum = xs.sum := by
  simp [sum_reverse]

theorem sum_eq_foldl_int {xs : Array Int} : xs.sum = xs.foldl (init := 0) (· + ·) := by
  simp only [foldl_eq_foldr_reverse, Int.add_comm, ← sum_eq_foldr, sum_reverse_int]

end Array
