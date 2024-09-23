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

attribute [bv_normalize] not_true
attribute [bv_normalize] and_true_eq
attribute [bv_normalize] true_and_eq
attribute [bv_normalize] or_true_eq
attribute [bv_normalize] true_or_eq

end Frontend.Normalize
end Std.Tactic.BVDecide
