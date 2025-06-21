/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.Ordered.Ring
import Init.GrindInstances.Ring.Int
import Init.Omega

/-!
# `grind` instances for `Int` as an ordered module.
-/

namespace Lean.Grind

instance : Preorder Int where
  le_refl := Int.le_refl
  le_trans := Int.le_trans
  lt_iff_le_not_le := by omega

instance : OrderedAdd Int where
  add_le_left_iff := by omega

instance : OrderedRing Int where
  zero_lt_one := by omega
  mul_lt_mul_of_pos_left := Int.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := Int.mul_lt_mul_of_pos_right

end Lean.Grind
