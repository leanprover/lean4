/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Grind.CommRing.Basic
import Init.Data.SInt.Lemmas

namespace Lean.Grind

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
  left_distrib _ _ _ := Int8.mul_add
  zero_mul _ := Int8.zero_mul
  cast_add := Int8.ofInt_add
  cast_mul := Int8.ofInt_mul
  cast_neg := Int8.ofInt_neg

instance : IsCharP Int8 (2 ^ 8) where
  char {x} := by
    simp [Int.cast, IntCast.intCast, Int8.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_emod_eq_zero, ← Int.dvd_iff_bmod_eq_zero]

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
  left_distrib _ _ _ := Int16.mul_add
  zero_mul _ := Int16.zero_mul
  cast_add := Int16.ofInt_add
  cast_mul := Int16.ofInt_mul
  cast_neg := Int16.ofInt_neg

instance : IsCharP Int16 (2 ^ 16) where
  char {x} := by
    simp [Int.cast, IntCast.intCast, Int16.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_emod_eq_zero, ← Int.dvd_iff_bmod_eq_zero]

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
  left_distrib _ _ _ := Int32.mul_add
  zero_mul _ := Int32.zero_mul
  cast_add := Int32.ofInt_add
  cast_mul := Int32.ofInt_mul
  cast_neg := Int32.ofInt_neg

instance : IsCharP Int32 (2 ^ 32) where
  char {x} := by
    simp [Int.cast, IntCast.intCast, Int32.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_emod_eq_zero, ← Int.dvd_iff_bmod_eq_zero]

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
  left_distrib _ _ _ := Int64.mul_add
  zero_mul _ := Int64.zero_mul
  cast_add := Int64.ofInt_add
  cast_mul := Int64.ofInt_mul
  cast_neg := Int64.ofInt_neg

instance : IsCharP Int64 (2 ^ 64) where
  char {x} := by
    simp [Int.cast, IntCast.intCast, Int64.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_emod_eq_zero, ← Int.dvd_iff_bmod_eq_zero]

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
  left_distrib _ _ _ := ISize.mul_add
  zero_mul _ := ISize.zero_mul
  cast_add := ISize.ofInt_add
  cast_mul := ISize.ofInt_mul
  cast_neg := ISize.ofInt_neg

open System.Platform (numBits)

instance : IsCharP ISize (2 ^ numBits) where
  char {x} := by
    simp [Int.cast, IntCast.intCast, ISize.ofInt_eq_iff_bmod_eq_toInt,
      ← Int.dvd_iff_emod_eq_zero, ← Int.dvd_iff_bmod_eq_zero]

end Lean.Grind
