/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
prelude

import Init.Grind.Module.Basic
import Init.Grind.Ring.Basic

namespace Lean.Grind

instance : AddRightCancel Nat where
  add_right_cancel _ _ _ := Nat.add_right_cancel

instance : CommSemiring Nat where
  add := Nat.add
  mul := Nat.mul
  hPow := Nat.pow
  add_assoc := Nat.add_assoc
  add_comm := Nat.add_comm
  add_zero := Nat.add_zero
  mul_assoc := Nat.mul_assoc
  mul_comm := Nat.mul_comm
  mul_one := Nat.mul_one
  one_mul := Nat.one_mul
  zero_mul := Nat.zero_mul
  mul_zero := Nat.mul_zero
  left_distrib := Nat.left_distrib
  right_distrib := Nat.right_distrib
  pow_zero := Nat.pow_zero
  pow_succ := Nat.pow_succ

instance : NoNatZeroDivisors Nat where
  no_nat_zero_divisors := by
    intro k a b h₁ h₂
    exact Nat.mul_left_cancel (Nat.zero_lt_of_ne_zero h₁) h₂

instance : IsCharP Nat 0 where
  ofNat_ext_iff := by intro; simp [OfNat.ofNat]

end Lean.Grind
