/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind.Ring.Basic
public import all Init.Grind.ToInt
public import Init.GrindInstances.ToInt
public import all Init.Data.BitVec.Basic
public import all Init.Data.SInt.Basic
public import Init.Data.SInt.Lemmas

public section

namespace Lean.Grind

instance : NatCast Int8 where
  natCast x := Int8.ofNat x

instance : IntCast Int8 where
  intCast x := Int8.ofInt x

instance : CommRing Int8 where
  add_assoc := Int8.add_assoc
  add_comm := Int8.add_comm
  add_zero := Int8.add_zero
  neg_add_cancel := Int8.add_left_neg
  mul_assoc := Int8.mul_assoc
  mul_comm := Int8.mul_comm
  mul_one := Int8.mul_one
  one_mul := Int8.one_mul
  left_distrib _ _ _ := Int8.mul_add
  right_distrib _ _ _ := Int8.add_mul
  zero_mul _ := Int8.zero_mul
  mul_zero _ := Int8.mul_zero
  sub_eq_add_neg := Int8.sub_eq_add_neg
  pow_zero := Int8.pow_zero
  pow_succ := Int8.pow_succ
  ofNat_succ x := Int8.ofNat_add x 1
  intCast_neg := Int8.ofInt_neg

instance : IsCharP Int8 (2 ^ 8) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = Int8.ofInt x := rfl
    rw [this]
    simp [Int8.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_bmod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Int.ofNat_dvd_right])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add Int8 (.sint 8) := inferInstance
example : ToInt.Neg Int8 (.sint 8) := inferInstance
example : ToInt.Sub Int8 (.sint 8) := inferInstance

instance : ToInt.Pow Int8 (.sint 8) := ToInt.pow_of_semiring (by simp)

instance : NatCast Int16 where
  natCast x := Int16.ofNat x

instance : IntCast Int16 where
  intCast x := Int16.ofInt x

instance : CommRing Int16 where
  add_assoc := Int16.add_assoc
  add_comm := Int16.add_comm
  add_zero := Int16.add_zero
  neg_add_cancel := Int16.add_left_neg
  mul_assoc := Int16.mul_assoc
  mul_comm := Int16.mul_comm
  mul_one := Int16.mul_one
  one_mul := Int16.one_mul
  left_distrib _ _ _ := Int16.mul_add
  right_distrib _ _ _ := Int16.add_mul
  zero_mul _ := Int16.zero_mul
  mul_zero _ := Int16.mul_zero
  sub_eq_add_neg := Int16.sub_eq_add_neg
  pow_zero := Int16.pow_zero
  pow_succ := Int16.pow_succ
  ofNat_succ x := Int16.ofNat_add x 1
  intCast_neg := Int16.ofInt_neg

instance : IsCharP Int16 (2 ^ 16) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = Int16.ofInt x := rfl
    rw [this]
    simp [Int16.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_bmod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Int.ofNat_dvd_right])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add Int16 (.sint 16) := inferInstance
example : ToInt.Neg Int16 (.sint 16) := inferInstance
example : ToInt.Sub Int16 (.sint 16) := inferInstance

instance : ToInt.Pow Int16 (.sint 16) := ToInt.pow_of_semiring (by simp)

instance : NatCast Int32 where
  natCast x := Int32.ofNat x

instance : IntCast Int32 where
  intCast x := Int32.ofInt x

instance : CommRing Int32 where
  add_assoc := Int32.add_assoc
  add_comm := Int32.add_comm
  add_zero := Int32.add_zero
  neg_add_cancel := Int32.add_left_neg
  mul_assoc := Int32.mul_assoc
  mul_comm := Int32.mul_comm
  mul_one := Int32.mul_one
  one_mul := Int32.one_mul
  left_distrib _ _ _ := Int32.mul_add
  right_distrib _ _ _ := Int32.add_mul
  zero_mul _ := Int32.zero_mul
  mul_zero _ := Int32.mul_zero
  sub_eq_add_neg := Int32.sub_eq_add_neg
  pow_zero := Int32.pow_zero
  pow_succ := Int32.pow_succ
  ofNat_succ x := Int32.ofNat_add x 1
  intCast_neg := Int32.ofInt_neg

instance : IsCharP Int32 (2 ^ 32) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = Int32.ofInt x := rfl
    rw [this]
    simp [Int32.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_bmod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Int.ofNat_dvd_right])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add Int32 (.sint 32) := inferInstance
example : ToInt.Neg Int32 (.sint 32) := inferInstance
example : ToInt.Sub Int32 (.sint 32) := inferInstance

instance : ToInt.Pow Int32 (.sint 32) := ToInt.pow_of_semiring (by simp)

instance : NatCast Int64 where
  natCast x := Int64.ofNat x

instance : IntCast Int64 where
  intCast x := Int64.ofInt x

instance : CommRing Int64 where
  add_assoc := Int64.add_assoc
  add_comm := Int64.add_comm
  add_zero := Int64.add_zero
  neg_add_cancel := Int64.add_left_neg
  mul_assoc := Int64.mul_assoc
  mul_comm := Int64.mul_comm
  mul_one := Int64.mul_one
  one_mul := Int64.one_mul
  left_distrib _ _ _ := Int64.mul_add
  right_distrib _ _ _ := Int64.add_mul
  zero_mul _ := Int64.zero_mul
  mul_zero _ := Int64.mul_zero
  sub_eq_add_neg := Int64.sub_eq_add_neg
  pow_zero := Int64.pow_zero
  pow_succ := Int64.pow_succ
  ofNat_succ x := Int64.ofNat_add x 1
  intCast_neg := Int64.ofInt_neg

instance : IsCharP Int64 (2 ^ 64) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = Int64.ofInt x := rfl
    rw [this]
    simp [Int64.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_bmod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Int.ofNat_dvd_right])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add Int64 (.sint 64) := inferInstance
example : ToInt.Neg Int64 (.sint 64) := inferInstance
example : ToInt.Sub Int64 (.sint 64) := inferInstance

instance : ToInt.Pow Int64 (.sint 64) := ToInt.pow_of_semiring (by simp)

instance : NatCast ISize where
  natCast x := ISize.ofNat x

instance : IntCast ISize where
  intCast x := ISize.ofInt x

instance : CommRing ISize where
  add_assoc := ISize.add_assoc
  add_comm := ISize.add_comm
  add_zero := ISize.add_zero
  neg_add_cancel := ISize.add_left_neg
  mul_assoc := ISize.mul_assoc
  mul_comm := ISize.mul_comm
  mul_one := ISize.mul_one
  one_mul := ISize.one_mul
  left_distrib _ _ _ := ISize.mul_add
  right_distrib _ _ _ := ISize.add_mul
  zero_mul _ := ISize.zero_mul
  mul_zero _ := ISize.mul_zero
  sub_eq_add_neg := ISize.sub_eq_add_neg
  pow_zero := ISize.pow_zero
  pow_succ := ISize.pow_succ
  ofNat_succ x := ISize.ofNat_add x 1
  intCast_neg := ISize.ofInt_neg
open System.Platform (numBits)

instance : IsCharP ISize (2 ^ numBits) := IsCharP.mk' _ _
  (ofNat_eq_zero_iff := fun x => by
    have : OfNat.ofNat x = ISize.ofInt x := rfl
    rw [this]
    simp [ISize.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_bmod_eq_zero, ← Nat.dvd_iff_mod_eq_zero, Int.ofNat_dvd_right])

-- Verify we can derive the instances showing how `toInt` interacts with operations:
example : ToInt.Add ISize (.sint numBits) := inferInstance
example : ToInt.Neg ISize (.sint numBits) := inferInstance
example : ToInt.Sub ISize (.sint numBits) := inferInstance

instance : ToInt.Pow ISize (.sint numBits) :=
  ToInt.pow_of_semiring (by simp)

end Lean.Grind
