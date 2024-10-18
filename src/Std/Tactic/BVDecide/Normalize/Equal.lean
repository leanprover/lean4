/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.Data.Bool
import Init.Data.BitVec

/-!
This module contains the equality simplifying part of the `bv_normalize` simp set.
-/

namespace Std.Tactic.BVDecide
namespace Frontend.Normalize

attribute [bv_normalize] beq_true
attribute [bv_normalize] Bool.true_beq
attribute [bv_normalize] beq_false
attribute [bv_normalize] Bool.false_beq
attribute [bv_normalize] beq_self_eq_true
attribute [bv_normalize] beq_self_eq_true'

@[bv_normalize]
theorem Bool.not_beq_not : ∀ (a b : Bool), ((!a) == (!b)) = (a == b) := by
  decide

@[bv_normalize]
theorem BitVec.not_beq_not (a b : BitVec w) : (~~~a == ~~~b) = (a == b) := by
  match h : a == b with
  | true => simp_all
  | false =>
    simp only [beq_eq_false_iff_ne, ne_eq] at *
    bv_omega

end Frontend.Normalize
end Std.Tactic.BVDecide
