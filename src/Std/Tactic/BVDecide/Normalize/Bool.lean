/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.SimpLemmas
import Init.Data.Bool

/-!
This module contains the `Bool` simplifying part of the `bv_normalize` simp set.
-/

namespace Std.Tactic.BVDecide
namespace Normalize

attribute [bv_normalize] Bool.not_true
attribute [bv_normalize] Bool.not_false
attribute [bv_normalize] Bool.and_true
attribute [bv_normalize] Bool.true_and
attribute [bv_normalize] Bool.and_false
attribute [bv_normalize] Bool.false_and
attribute [bv_normalize] beq_self_eq_true'
attribute [bv_normalize] Bool.true_beq
attribute [bv_normalize] Bool.false_beq
attribute [bv_normalize] Bool.beq_not_self
attribute [bv_normalize] Bool.not_beq_self
attribute [bv_normalize] Bool.beq_self_left
attribute [bv_normalize] Bool.beq_self_right
attribute [bv_normalize] Bool.and_self
attribute [bv_normalize] Bool.and_not_self
attribute [bv_normalize] Bool.not_and_self
attribute [bv_normalize] Bool.xor_self
attribute [bv_normalize] Bool.xor_false
attribute [bv_normalize] Bool.false_xor
attribute [bv_normalize] Bool.true_xor
attribute [bv_normalize] Bool.xor_true
attribute [bv_normalize] Bool.not_xor_self
attribute [bv_normalize] Bool.xor_not_self
attribute [bv_normalize] Bool.not_not
attribute [bv_normalize] Bool.and_self_left
attribute [bv_normalize] Bool.and_self_right
attribute [bv_normalize] eq_self
attribute [bv_normalize] ite_self

@[bv_normalize]
theorem Bool.not_xor : ∀ (a b : Bool), !(a ^^ b) = (a == b) := by decide

@[bv_normalize]
theorem Bool.or_elim : ∀ (a b : Bool), (a || b) = !(!a && !b) := by decide

theorem Bool.and_left (lhs rhs : Bool) (h : (lhs && rhs) = true) : lhs = true := by
  revert lhs rhs
  decide

theorem Bool.and_right (lhs rhs : Bool) (h : (lhs && rhs) = true) : rhs = true := by
  revert lhs rhs
  decide

end Normalize
end Std.Tactic.BVDecide

