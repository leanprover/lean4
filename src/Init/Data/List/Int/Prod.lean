/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Data.List.Lemmas
import Init.Data.Int.Lemmas
public import Init.Data.Int.Pow
public import Init.Data.List.Basic

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace List

@[simp]
theorem prod_replicate_int {n : Nat} {a : Int} : (replicate n a).prod = a ^ n := by
  induction n <;> simp_all [replicate_succ, Int.pow_succ, Int.mul_comm]

theorem prod_append_int {l₁ l₂ : List Int} : (l₁ ++ l₂).prod = l₁.prod * l₂.prod := by
  simp [prod_append]

theorem prod_reverse_int (xs : List Int) : xs.reverse.prod = xs.prod := by
  simp [prod_reverse]

end List
