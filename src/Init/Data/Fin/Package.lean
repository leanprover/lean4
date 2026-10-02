/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julia M. Himmel
-/
module

prelude
public import Init.Data.Order.PackageFactories
public import Init.Data.Fin.MinMax
import Init.Data.Fin.Lemmas
import Init.Data.Order.Lemmas
import Init.Data.Nat.Compare
import Init.ByCases
import Init.Data.Nat.Order

open Std

namespace Fin

@[simp]
public theorem compare_val {n : Nat} (a b : Fin n) : compare (a : Nat) (b : Nat) = compare a b := rfl

public instance {n : Nat} : LinearOrderPackage (Fin n) := .ofLE _ {
  beq_iff_le_and_ge a b := by simpa using Fin.le_antisymm_iff
  isLE_compare a b := by rw [le_def, ← isLE_compare, compare_val]
  isGE_compare a b := by rw [le_def, ← isGE_compare, compare_val]
  min_eq a b := by simp [← val_inj, val_min, apply_ite val, min_eq_ite, le_def]
  max_eq a b := by simp [← val_inj, val_max, apply_ite val, max_eq_ite, le_def]
}

end Fin
