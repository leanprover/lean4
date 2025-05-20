/-
Copyright (c) 2025 Lean FRO, LLC. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

prelude
import Init.Grind.Module.Basic
import Init.Grind.CommRing.Int
import Init.Omega

/-!
# `grind` instances for `Int` as an ordered module.
-/

namespace Lean.Grind

instance : Preorder Int where
  le_refl := Int.le_refl
  le_trans _ _ _ := Int.le_trans
  lt_iff_le_not_le := by omega

instance : IntModule.IsOrdered Int where
  neg_le_iff := by omega
  neg_lt_iff := by omega
  add_lt_left := by omega
  add_lt_right := by omega
  hmul_pos k a ha := ⟨fun hk => Int.mul_pos hk ha, fun h => Int.pos_of_mul_pos_left h ha⟩
  hmul_neg k a ha := ⟨fun hk => Int.mul_neg_of_pos_of_neg hk ha, fun h => Int.pos_of_mul_neg_left h ha⟩
  hmul_nonpos k a ha hk := Int.mul_nonpos_of_nonneg_of_nonpos hk ha
  hmul_nonneg k a ha hk := Int.mul_nonneg hk ha

end Lean.Grind
