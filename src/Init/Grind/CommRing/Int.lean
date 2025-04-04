/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
prelude
import Init.Grind.CommRing.Basic
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
  left_distrib := Int.mul_add
  zero_mul := Int.zero_mul

end Lean.Grind
