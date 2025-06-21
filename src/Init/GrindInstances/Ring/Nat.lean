/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.Ring.Basic
import Init.Data.Int.Lemmas

namespace Lean.Grind

instance : CommSemiring Nat where
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  add_zero := Nat.add_zero
  mul_assoc := Nat.mul_assoc
  mul_comm := Nat.mul_comm
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  left_distrib := Nat.mul_add
  right_distrib := Nat.add_mul
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  pow_zero _ := by rfl
  pow_succ _ _ := by rfl
  ofNat_succ _ := by rfl

instance : IsCharP Nat 0 where
  ofNat_ext_iff {x y} := by simp [OfNat.ofNat]

instance : NoNatZeroDivisors Nat where
  no_nat_zero_divisors _ _ _ h₁ h₂ := (Nat.mul_right_inj h₁).mp h₂

end Lean.Grind
