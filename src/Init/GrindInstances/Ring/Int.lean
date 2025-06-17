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

instance : CommRing Int where
  add_assoc := Int.add_assoc
  add_comm := Int.add_comm
  add_zero := Int.add_zero
  neg_add_cancel := Int.add_left_neg
  mul_assoc := Int.mul_assoc
  mul_comm := Int.mul_comm
  mul_one := Int.mul_one
  one_mul := Int.one_mul
  left_distrib := Int.mul_add
  right_distrib := Int.add_mul
  zero_mul := Int.zero_mul
  mul_zero := Int.mul_zero
  pow_zero _ := by rfl
  pow_succ _ _ := by rfl
  ofNat_succ _ := by rfl
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg

instance : IsCharP Int 0 where
  ofNat_eq_zero_iff {x} := by erw [Int.ofNat_eq_zero]; simp

instance : NoNatZeroDivisors Int where
  no_nat_zero_divisors k a h₁ h₂ := by
    cases Int.mul_eq_zero.mp h₂
    next h =>
      rw [← Int.natCast_zero] at h
      have h : (k : Int).toNat = (↑0 : Int).toNat := congrArg Int.toNat h;
      simp at h
      contradiction
    next => assumption

end Lean.Grind
