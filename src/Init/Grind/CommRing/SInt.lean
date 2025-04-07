/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Grind.CommRing.Basic
import Init.Data.SInt.Lemmas

namespace Lean.Grind

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

end Lean.Grind
