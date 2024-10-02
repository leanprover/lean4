/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Henrik Böving
-/
prelude
import Init.SimpLemmas

/-!
This module contains the `Prop` simplifying part of the `bv_normalize` simp set.
-/

namespace Std.Tactic.BVDecide
namespace Frontend.Normalize

attribute [bv_normalize] ite_true
attribute [bv_normalize] ite_false
attribute [bv_normalize] dite_true
attribute [bv_normalize] dite_false
attribute [bv_normalize] and_true
attribute [bv_normalize] true_and
attribute [bv_normalize] and_false
attribute [bv_normalize] false_and
attribute [bv_normalize] or_true
attribute [bv_normalize] true_or
attribute [bv_normalize] or_false
attribute [bv_normalize] false_or
attribute [bv_normalize] iff_true
attribute [bv_normalize] true_iff
attribute [bv_normalize] iff_false
attribute [bv_normalize] false_iff
attribute [bv_normalize] false_implies
attribute [bv_normalize] imp_false
attribute [bv_normalize] implies_true
attribute [bv_normalize] true_implies
attribute [bv_normalize] not_true
attribute [bv_normalize] not_false_iff
attribute [bv_normalize] eq_iff_iff

end Frontend.Normalize
end Std.Tactic.BVDecide
