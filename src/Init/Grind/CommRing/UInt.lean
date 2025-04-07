/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Grind.CommRing.Basic
import Init.Data.UInt.Lemmas

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

end Lean.Grind
