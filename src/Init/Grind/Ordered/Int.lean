/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
public import Init.Grind.Ordered.Ring
public import Init.GrindInstances.Ring.Int
public import Init.Omega

public section

/-!
# `grind` instances for `Int` as an ordered module.
-/

open Std

namespace Lean.Grind

instance : IsLinearOrder Int where
  le_refl := Int.le_refl
  le_trans _ _ _ := Int.le_trans
  le_antisymm _ _ := Int.le_antisymm
  le_total := Int.le_total

instance : LawfulOrderLT Int where
  lt_iff := by omega

instance : OrderedAdd Int where
  add_le_left_iff := by omega

instance : OrderedRing Int where
  zero_lt_one := by omega
  mul_lt_mul_of_pos_left := Int.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := Int.mul_lt_mul_of_pos_right

end Lean.Grind
