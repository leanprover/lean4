/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Robin Arnez
-/
module

prelude
public import Init.Data.Dyadic.Basic
public import Init.Grind.Ring.Basic
public import Init.Grind.Ordered.Ring

/-! # Internal `grind` algebra instances for `Dyadic`. -/

open Lean.Grind

namespace Dyadic

instance : CommRing Dyadic where
  nsmul := ⟨(· * ·)⟩
  zsmul := ⟨(· * ·)⟩
  add_zero := Dyadic.add_zero
  add_comm := Dyadic.add_comm
  add_assoc := Dyadic.add_assoc
  mul_assoc := Dyadic.mul_assoc
  mul_one := Dyadic.mul_one
  one_mul := Dyadic.one_mul
  zero_mul := Dyadic.zero_mul
  mul_zero := Dyadic.mul_zero
  mul_comm := Dyadic.mul_comm
  pow_zero := Dyadic.pow_zero
  pow_succ := Dyadic.pow_succ
  sub_eq_add_neg _ _ := rfl
  neg_add_cancel := Dyadic.neg_add_cancel
  neg_zsmul i a := by
    change ((-i : Int) : Dyadic) * a = -(i * a)
    simp [← toRat_inj, Rat.neg_mul]
  left_distrib := Dyadic.mul_add
  right_distrib := Dyadic.add_mul
  intCast_neg _ := by simp [← toRat_inj]
  ofNat_succ n := by
    change ((n + 1 : Int) : Dyadic) = ((n : Int) : Dyadic) + 1
    simp [← toRat_inj, Rat.intCast_add]; rfl

instance : IsCharP Dyadic 0 := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by change (x : Dyadic) = 0 ↔ _; simp [← toRat_inj])

instance : NoNatZeroDivisors Dyadic where
  no_nat_zero_divisors k a b h₁ h₂ := by
    change k * a = k * b at h₂
    simp only [← toRat_inj, toRat_mul, toRat_natCast] at h₂ ⊢
    simpa [← Rat.mul_assoc, Rat.inv_mul_cancel, h₁] using congrArg ((k : Rat)⁻¹ * ·) h₂

instance : LinearOrder Dyadic where
  le_refl := Dyadic.le_refl
  le_trans := Dyadic.le_trans
  le_antisymm := Dyadic.le_antisymm
  le_total := Dyadic.le_total
  lt_iff_le_not_le := Std.LawfulOrderLT.lt_iff _ _

instance : OrderedRing Dyadic where
  zero_lt_one := by decide
  add_le_left_iff _ := by simp [le_iff_toRat, Rat.add_le_add_right]
  mul_lt_mul_of_pos_left {_ _ _} := by simpa [lt_iff_toRat] using Rat.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right {_ _ _} := by simpa [lt_iff_toRat] using Rat.mul_lt_mul_of_pos_right

end Dyadic
