/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind.Ring.Basic
public import Init.Data.Int.Lemmas

public section

namespace Lean.Grind

instance : CommRing Int where
  nsmul := ⟨(· * ·)⟩
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
  neg_zsmul := Int.neg_mul

instance : IsCharP Int 0 := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by erw [Int.ofNat_eq_zero]; simp)

instance : NoNatZeroDivisors Int where
  no_nat_zero_divisors k a b h₁ h₂ := by
    replace h₁ : (k : Int) ≠ 0 := by simp [h₁]
    cases Int.mul_eq_mul_left_iff h₁ |>.mp h₂
    rfl

end Lean.Grind
