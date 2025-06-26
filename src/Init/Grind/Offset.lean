/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
module

prelude
import Init.Core
import Init.Omega

namespace Lean.Grind
abbrev isLt (x y : Nat) : Bool := x < y
abbrev isLE (x y : Nat) : Bool := x ≤ y

/-! Theorems for transitivity. -/
theorem Nat.le_ro (u w v k : Nat) : u ≤ w → w ≤ v + k → u ≤ v + k := by
  omega
theorem Nat.le_lo (u w v k : Nat) : u ≤ w → w + k ≤ v → u + k ≤ v := by
  omega
theorem Nat.lo_le (u w v k : Nat) : u + k ≤ w → w ≤ v → u + k ≤ v := by
  omega
theorem Nat.lo_lo (u w v k₁ k₂ : Nat) : u + k₁ ≤ w → w + k₂ ≤ v → u + (k₁ + k₂) ≤ v := by
  omega
theorem Nat.lo_ro_1 (u w v k₁ k₂ : Nat) : isLt k₂ k₁ = true → u + k₁ ≤ w → w ≤ v + k₂ → u + (k₁ - k₂) ≤ v := by
  simp [isLt]; omega
theorem Nat.lo_ro_2 (u w v k₁ k₂ : Nat) : u + k₁ ≤ w → w ≤ v + k₂ → u ≤ v + (k₂ - k₁) := by
  omega
theorem Nat.ro_le (u w v k : Nat) : u ≤ w + k → w ≤ v → u ≤ v + k := by
  omega
theorem Nat.ro_lo_1 (u w v k₁ k₂ : Nat) : u ≤ w + k₁ → w + k₂ ≤ v → u ≤ v + (k₁ - k₂) := by
  omega
theorem Nat.ro_lo_2 (u w v k₁ k₂ : Nat) : isLt k₁ k₂ = true → u ≤ w + k₁ → w + k₂ ≤ v → u + (k₂ - k₁) ≤ v := by
  simp [isLt]; omega
theorem Nat.ro_ro (u w v k₁ k₂ : Nat) : u ≤ w + k₁ → w ≤ v + k₂ → u ≤ v + (k₁ + k₂) := by
  omega

/-! Theorems for negating constraints. -/
theorem Nat.of_le_eq_false (u v : Nat) : ((u ≤ v) = False) → v + 1 ≤ u := by
  simp; omega
theorem Nat.of_lo_eq_false_1 (u v : Nat) : ((u + 1 ≤ v) = False) → v ≤ u := by
  simp; omega
theorem Nat.of_lo_eq_false (u v k : Nat) : ((u + k ≤ v) = False) → v ≤ u + (k-1) := by
  simp; omega
theorem Nat.of_ro_eq_false (u v k : Nat) : ((u ≤ v + k) = False) → v + (k+1) ≤ u := by
  simp; omega

/-! Theorems for closing a goal. -/
theorem Nat.unsat_le_lo (u v k : Nat) : isLt 0 k = true → u ≤ v → v + k ≤ u → False := by
  simp [isLt]; omega
theorem Nat.unsat_lo_lo (u v k₁ k₂ : Nat) : isLt 0 (k₁+k₂) = true → u + k₁ ≤ v → v + k₂ ≤ u → False := by
  simp [isLt]; omega
theorem Nat.unsat_lo_ro (u v k₁ k₂ : Nat) : isLt k₂ k₁ = true → u + k₁ ≤ v → v ≤ u + k₂ → False := by
  simp [isLt]; omega

/-! Theorems for propagating constraints to `True` -/
theorem Nat.lo_eq_true_of_lo (u v k₁ k₂ : Nat) : isLE k₂ k₁ = true → u + k₁ ≤ v → (u + k₂ ≤ v) = True :=
  by simp; omega
theorem Nat.le_eq_true_of_lo (u v k : Nat) : u + k ≤ v → (u ≤ v) = True :=
  by simp; omega
theorem Nat.le_eq_true_of_le (u v : Nat) : u ≤ v → (u ≤ v) = True :=
  by simp
theorem Nat.ro_eq_true_of_lo (u v k₁ k₂ : Nat) : u + k₁ ≤ v → (u ≤ v + k₂) = True :=
  by simp; omega
theorem Nat.ro_eq_true_of_le (u v k : Nat) : u ≤ v → (u ≤ v + k) = True :=
  by simp; omega
theorem Nat.ro_eq_true_of_ro (u v k₁ k₂ : Nat) : isLE k₁ k₂ = true → u ≤ v + k₁ → (u ≤ v + k₂) = True :=
  by simp [isLE]; omega

/-!
Theorems for propagating constraints to `False`.
They are variants of the theorems for closing a goal.
-/
theorem Nat.lo_eq_false_of_le (u v k : Nat) : isLt 0 k = true → u ≤ v → (v + k ≤ u) = False := by
 simp [isLt]; omega
theorem Nat.le_eq_false_of_lo (u v k : Nat) : isLt 0 k = true → u + k ≤ v → (v ≤ u) = False := by
 simp [isLt]; omega
theorem Nat.lo_eq_false_of_lo (u v k₁ k₂ : Nat) : isLt 0 (k₁+k₂) = true → u + k₁ ≤ v → (v + k₂ ≤ u) = False := by
  simp [isLt]; omega
theorem Nat.ro_eq_false_of_lo (u v k₁ k₂ : Nat) : isLt k₂ k₁ = true → u + k₁ ≤ v → (v ≤ u + k₂) = False := by
  simp [isLt]; omega
theorem Nat.lo_eq_false_of_ro (u v k₁ k₂ : Nat) : isLt k₁ k₂ = true → u ≤ v + k₁ → (v + k₂ ≤ u) = False := by
  simp [isLt]; omega

/-!
Helper theorems for equality propagation
-/

theorem Nat.le_of_eq_1 (u v : Nat) : u = v → u ≤ v := by omega
theorem Nat.le_of_eq_2 (u v : Nat) : u = v → v ≤ u := by omega
theorem Nat.eq_of_le_of_le (u v : Nat) : u ≤ v → v ≤ u → u = v := by omega
theorem Nat.le_offset (a k : Nat) : k ≤ a + k := by omega

end Lean.Grind
