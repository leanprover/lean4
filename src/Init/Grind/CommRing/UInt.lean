/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Grind.CommRing.Basic
import Init.Data.UInt.Lemmas


namespace UInt8

/-- Variant of `UInt8.ofNat_mod_size` replacing `2 ^ 8` with `256`.-/
theorem ofNat_mod_size' : ofNat (x % 256) = ofNat x := ofNat_mod_size

instance : IntCast UInt8 where
  intCast x := UInt8.ofInt x

end UInt8

namespace UInt16

/-- Variant of `UInt16.ofNat_mod_size` replacing `2 ^ 16` with `65536`.-/
theorem ofNat_mod_size' : ofNat (x % 65536) = ofNat x := ofNat_mod_size

instance : IntCast UInt16 where
  intCast x := UInt16.ofInt x

end UInt16

namespace UInt32

/-- Variant of `UInt32.ofNat_mod_size` replacing `2 ^ 32` with `4294967296`.-/
theorem ofNat_mod_size' : ofNat (x % 4294967296) = ofNat x := ofNat_mod_size

instance : IntCast UInt32 where
  intCast x := UInt32.ofInt x

end UInt32

namespace UInt64

/-- Variant of `UInt64.ofNat_mod_size` replacing `2 ^ 64` with `18446744073709551616`.-/
theorem ofNat_mod_size' : ofNat (x % 18446744073709551616) = ofNat x := ofNat_mod_size

instance : IntCast UInt64 where
  intCast x := UInt64.ofInt x

end UInt64

namespace USize

instance : IntCast USize where
  intCast x := USize.ofInt x

end USize
namespace Lean.Grind

instance : CommRing UInt8 where
  add_assoc := UInt8.add_assoc
  add_comm := UInt8.add_comm
  add_zero := UInt8.add_zero
  neg_add_cancel := UInt8.add_left_neg
  mul_assoc := UInt8.mul_assoc
  mul_comm := UInt8.mul_comm
  mul_one := UInt8.mul_one
  left_distrib _ _ _ := UInt8.mul_add
  zero_mul _ := UInt8.zero_mul
  sub_eq_add_neg := UInt8.sub_eq_add_neg
  pow_zero := UInt8.pow_zero
  pow_succ := UInt8.pow_succ
  ofNat_succ x := UInt8.ofNat_add x 1

instance : IsCharP UInt8 (2 ^ 8) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = UInt8.ofNat x := rfl
    simp [this, UInt8.ofNat_eq_iff_mod_eq_toNat]

instance : CommRing UInt16 where
  add_assoc := UInt16.add_assoc
  add_comm := UInt16.add_comm
  add_zero := UInt16.add_zero
  neg_add_cancel := UInt16.add_left_neg
  mul_assoc := UInt16.mul_assoc
  mul_comm := UInt16.mul_comm
  mul_one := UInt16.mul_one
  left_distrib _ _ _ := UInt16.mul_add
  zero_mul _ := UInt16.zero_mul
  sub_eq_add_neg := UInt16.sub_eq_add_neg
  pow_zero := UInt16.pow_zero
  pow_succ := UInt16.pow_succ
  ofNat_succ x := UInt16.ofNat_add x 1

instance : IsCharP UInt16 (2 ^ 16) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = UInt16.ofNat x := rfl
    simp [this, UInt16.ofNat_eq_iff_mod_eq_toNat]

instance : CommRing UInt32 where
  add_assoc := UInt32.add_assoc
  add_comm := UInt32.add_comm
  add_zero := UInt32.add_zero
  neg_add_cancel := UInt32.add_left_neg
  mul_assoc := UInt32.mul_assoc
  mul_comm := UInt32.mul_comm
  mul_one := UInt32.mul_one
  left_distrib _ _ _ := UInt32.mul_add
  zero_mul _ := UInt32.zero_mul
  sub_eq_add_neg := UInt32.sub_eq_add_neg
  pow_zero := UInt32.pow_zero
  pow_succ := UInt32.pow_succ
  ofNat_succ x := UInt32.ofNat_add x 1

instance : IsCharP UInt32 (2 ^ 32) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = UInt32.ofNat x := rfl
    simp [this, UInt32.ofNat_eq_iff_mod_eq_toNat]

instance : CommRing UInt64 where
  add_assoc := UInt64.add_assoc
  add_comm := UInt64.add_comm
  add_zero := UInt64.add_zero
  neg_add_cancel := UInt64.add_left_neg
  mul_assoc := UInt64.mul_assoc
  mul_comm := UInt64.mul_comm
  mul_one := UInt64.mul_one
  left_distrib _ _ _ := UInt64.mul_add
  zero_mul _ := UInt64.zero_mul
  sub_eq_add_neg := UInt64.sub_eq_add_neg
  pow_zero := UInt64.pow_zero
  pow_succ := UInt64.pow_succ
  ofNat_succ x := UInt64.ofNat_add x 1

instance : IsCharP UInt64 (2 ^ 64) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = UInt64.ofNat x := rfl
    simp [this, UInt64.ofNat_eq_iff_mod_eq_toNat]

instance : CommRing USize where
  add_assoc := USize.add_assoc
  add_comm := USize.add_comm
  add_zero := USize.add_zero
  neg_add_cancel := USize.add_left_neg
  mul_assoc := USize.mul_assoc
  mul_comm := USize.mul_comm
  mul_one := USize.mul_one
  left_distrib _ _ _ := USize.mul_add
  zero_mul _ := USize.zero_mul
  sub_eq_add_neg := USize.sub_eq_add_neg
  pow_zero := USize.pow_zero
  pow_succ := USize.pow_succ
  ofNat_succ x := USize.ofNat_add x 1

open System.Platform

instance : IsCharP USize (2 ^ numBits) where
  ofNat_eq_zero_iff {x} := by
    have : OfNat.ofNat x = USize.ofNat x := rfl
    simp [this, USize.ofNat_eq_iff_mod_eq_toNat]

end Lean.Grind
