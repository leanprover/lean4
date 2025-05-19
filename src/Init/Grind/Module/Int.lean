/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.Module.Basic
import Init.Omega

/-!
# `grind` instances for `Int` as an ordered module.
-/

namespace Lean.Grind

instance : IntModule Int where
  add_zero := Int.add_zero
  zero_add := Int.zero_add
  add_comm := Int.add_comm
  add_assoc := Int.add_assoc
  zero_smul := Int.zero_mul
  one_smul := Int.one_mul
  add_smul := Int.add_mul
  neg_smul := Int.neg_mul
  smul_zero := Int.mul_zero
  smul_add := Int.mul_add
  mul_smul := Int.mul_assoc
  neg_add_cancel := Int.add_left_neg
  sub_eq_add_neg _ _ := Int.sub_eq_add_neg

instance : Preorder Int where
  le_refl := Int.le_refl
  le_trans _ _ _ := Int.le_trans
  lt_iff_le_not_le := by omega

instance : IntModule.IsOrdered Int where
  neg_le_iff := by omega
  neg_lt_iff := by omega
  add_lt_left := by omega
  add_lt_right := by omega
  smul_pos k a ha := ⟨fun hk => Int.mul_pos hk ha, fun h => Int.pos_of_mul_pos_left h ha⟩
  smul_neg k a ha := ⟨fun hk => Int.mul_neg_of_pos_of_neg hk ha, fun h => Int.pos_of_mul_neg_left h ha⟩
  smul_nonpos k a ha hk := Int.mul_nonpos_of_nonneg_of_nonpos hk ha
  smul_nonneg k a ha hk := Int.mul_nonneg hk ha

end Lean.Grind
