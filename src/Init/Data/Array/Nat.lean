/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Graf, Paul Reichert
-/
module

prelude
public import Init.Data.Array.Lemmas
import Init.Data.List.Nat.Sum

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Array

protected theorem sum_pos_iff_exists_pos_nat {xs : Array Nat} : 0 < xs.sum ↔ ∃ x ∈ xs, 0 < x := by
  simp [← sum_toList, List.sum_pos_iff_exists_pos_nat]

protected theorem sum_eq_zero_iff_forall_eq_nat {xs : Array Nat} :
    xs.sum = 0 ↔ ∀ x ∈ xs, x = 0 := by
  simp [← sum_toList, List.sum_eq_zero_iff_forall_eq_nat]

@[simp] theorem sum_replicate_nat {n : Nat} {a : Nat} : (replicate n a).sum = n * a := by
  rw [← List.toArray_replicate, List.sum_toArray]
  simp

theorem sum_append_nat {as₁ as₂ : Array Nat} : (as₁ ++ as₂).sum = as₁.sum + as₂.sum := by
  simp [sum_append]

theorem sum_reverse_nat (xs : Array Nat) : xs.reverse.sum = xs.sum := by
  simp [sum_reverse]

theorem sum_eq_foldl_nat {xs : Array Nat} : xs.sum = xs.foldl (init := 0) (· + ·) := by
  simp only [foldl_eq_foldr_reverse, Nat.add_comm, ← sum_eq_foldr, sum_reverse_nat]

end Array
