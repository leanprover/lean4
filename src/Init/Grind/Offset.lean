/-
Copyright (c) 2025 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Init.Core
import Init.Omega

namespace Lean.Grind
def isLt (x y : Nat) : Bool := x < y

theorem Nat.le_ro (u w v k : Nat) : u ≤ w → w ≤ v + k → u ≤ v + k := by
  omega
theorem Nat.le_lo (u w v k : Nat) : u ≤ w → w + k ≤ v → u + k ≤ v := by
  omega
theorem Nat.lo_le (u w v k : Nat) : u + k ≤ w → w ≤ v → u + k ≤ v := by
  omega
theorem Nat.lo_lo (u w v k₁ k₂ : Nat) : u + k₁ ≤ w → w + k₂ ≤ v → u + (k₁ + k₂) ≤ v := by
  omega
theorem Nat.lo_ro_1 (u w v k₁ k₂ : Nat) : isLt k₂ k₁ = true → u + k₁ ≤ w → w ≤ v + k₂ → u + (k₁ - k₂) ≤ v := by
  simp [isLt]
  omega
theorem Nat.lo_ro_2 (u w v k₁ k₂ : Nat) : u + k₁ ≤ w → w ≤ v + k₂ → u ≤ v + (k₂ - k₁) := by
  omega
theorem Nat.ro_le (u w v k : Nat) : u ≤ w + k → w ≤ v → u ≤ v + k := by
  omega
theorem Nat.ro_lo_1 (u w v k₁ k₂ : Nat) : u ≤ w + k₁ → w + k₂ ≤ v → u ≤ v + (k₁ - k₂) := by
  omega
theorem Nat.ro_lo_2 (u w v k₁ k₂ : Nat) : isLt k₁ k₂ = true → u ≤ w + k₁ → w + k₂ ≤ v → u + (k₂ - k₁) ≤ v := by
  simp [isLt]
  omega
theorem Nat.ro_ro (u w v k₁ k₂ : Nat) : u ≤ w + k₁ → w ≤ v + k₂ → u ≤ v + (k₁ + k₂) := by
  omega

theorem Nat.of_le_eq_false (u v : Nat) : ((u ≤ v) = False) → v + 1 ≤ u := by
  simp; omega
theorem Nat.of_lo_eq_false_1 (u v : Nat) : ((u + 1 ≤ v) = False) → v ≤ u := by
  simp; omega
theorem Nat.of_lo_eq_false (u v k : Nat) : ((u + k ≤ v) = False) → v ≤ u + (k-1) := by
  simp; omega
theorem Nat.of_ro_eq_false (u v k : Nat) : ((u ≤ v + k) = False) → v + (k+1) ≤ u := by
  simp; omega

end Lean.Grind
