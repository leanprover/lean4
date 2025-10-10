/-
Copyright (c) 2025 Robin Arnez. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Init.Grind.Ring.Field
public import Init.Data.Rat.Lemmas

public section

namespace Lean.Grind

instance : Field Rat where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_assoc := Rat.add_assoc
  add_comm := Rat.add_comm
  add_zero := Rat.add_zero
  neg_add_cancel := Rat.neg_add_cancel
  mul_assoc := Rat.mul_assoc
  mul_comm := Rat.mul_comm
  mul_one := Rat.mul_one
  one_mul := Rat.one_mul
  left_distrib := Rat.mul_add
  right_distrib := Rat.add_mul
  zero_mul := Rat.zero_mul
  mul_zero := Rat.mul_zero
  pow_zero := Rat.pow_zero
  pow_succ := Rat.pow_succ
  ofNat_succ x := by
    change (((x + 1 : Nat) : Int) : Rat) = _
    simp only [Int.natCast_add, Int.cast_ofNat_Int, Rat.intCast_add]
    rfl
  sub_eq_add_neg := Rat.sub_eq_add_neg
  neg_zsmul i a := by
    change ((-i : Int) : Rat) * a = -(i * a)
    simp [Rat.intCast_neg, Rat.neg_mul]
  div_eq_mul_inv := Rat.div_def
  zero_ne_one := by decide
  inv_zero := Rat.inv_zero
  mul_inv_cancel := Rat.mul_inv_cancel _
  zpow_zero := Rat.zpow_zero
  zpow_succ := Rat.pow_succ
  zpow_neg := Rat.zpow_neg

instance : IsCharP Rat 0 := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    change ((x : Int) : Rat) = ((0 : Int) : Rat) ↔ _
    simp)

instance : NoNatZeroDivisors Rat where
  no_nat_zero_divisors k a b h₁ h₂ := by
    change k * a = k * b at h₂
    simpa [← Rat.mul_assoc, Rat.inv_mul_cancel, h₁] using congrArg ((k : Rat)⁻¹ * ·) h₂

end Lean.Grind
