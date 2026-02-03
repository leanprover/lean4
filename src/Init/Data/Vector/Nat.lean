/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Sebastian Graf, Paul Reichert
-/
module

prelude
public import Init.Data.Vector.Lemmas
public import Init.Data.Vector.Basic
import Init.Data.Array.Nat

public section

set_option linter.listVariables true -- Enforce naming conventions for `List`/`Array`/`Vector` variables.
set_option linter.indexVariables true -- Enforce naming conventions for index variables.

namespace Vector

protected theorem sum_pos_iff_exists_pos_nat {xs : Vector Nat n} : 0 < xs.sum ↔ ∃ x ∈ xs, 0 < x := by
  simp [← sum_toArray, Array.sum_pos_iff_exists_pos_nat]

protected theorem sum_eq_zero_iff_forall_eq_nat {xs : Vector Nat n} :
    xs.sum = 0 ↔ ∀ x ∈ xs, x = 0 := by
  simp [← sum_toArray, Array.sum_eq_zero_iff_forall_eq_nat]

@[simp] theorem sum_replicate_nat {n : Nat} {a : Nat} : (replicate n a).sum = n * a := by
  simp [← sum_toArray, Array.sum_replicate_nat]

theorem sum_append_nat {as₁ as₂ : Vector Nat n} : (as₁ ++ as₂).sum = as₁.sum + as₂.sum := by
  simp [← sum_toArray]

theorem sum_reverse_nat (xs : Vector Nat n) : xs.reverse.sum = xs.sum := by
  simp [sum_reverse]

theorem sum_eq_foldl_nat {xs : Vector Nat n} : xs.sum = xs.foldl (b := 0) (· + ·) := by
  simp only [foldl_eq_foldr_reverse, Nat.add_comm, ← sum_eq_foldr, sum_reverse_nat]

end Vector
