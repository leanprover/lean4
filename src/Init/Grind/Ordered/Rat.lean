/-
Copyright (c) 2025 Robin Arnez. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robin Arnez
-/
module

prelude
public import Init.Grind.Ordered.Ring
public import Init.GrindInstances.Ring.Rat
public import Init.Data.Rat.Lemmas

public section

/-!
# `grind` instances for `Rat` as an ordered module.
-/

namespace Lean.Grind

instance : LinearOrder Rat where
  le_refl _ := Rat.le_refl
  le_trans := Rat.le_trans
  lt_iff_le_not_le {a b} := by rw [← Rat.not_le, iff_and_self]; exact Rat.le_total.resolve_left
  le_antisymm := Rat.le_antisymm
  le_total _ _ := Rat.le_total

instance : OrderedAdd Rat where
  add_le_left_iff {a b} c := by simp [Rat.add_comm _ c, Rat.add_le_add_left]

instance : OrderedRing Rat where
  zero_lt_one := by decide
  mul_lt_mul_of_pos_left := Rat.mul_lt_mul_of_pos_left
  mul_lt_mul_of_pos_right := Rat.mul_lt_mul_of_pos_right

end Lean.Grind
