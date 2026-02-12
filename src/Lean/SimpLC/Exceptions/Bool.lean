/-
Copyright (c) 2024 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

prelude
import Init.Data.Bool
import Lean.SimpLC.Exceptions.Root

set_option Elab.async false -- `simplc` crashes on the command line with a 139 without this.

simp_lc allow Bool.bne_assoc Bool.bne_self_left -- `(x != (y != (x != (y != b)))) = b` `(y != (x != y)) = x`

#guard_msgs (drop info) in
simp_lc check in Bool

-- x y : Bool
-- ⊢ x = (y != (x != y))
simp_lc allow bne_self_eq_false Bool.bne_assoc

-- I'd expected that making `Decidable.em` a `@[simp]` would help here, but it doesn't seem to.
-- w : Decidable p
-- ⊢ p ∨ ¬p
simp_lc allow ite_else_decide_not_self Bool.if_true_left
-- w : Decidable p
-- ⊢ ¬p ∨ p
simp_lc allow ite_then_decide_self Bool.if_true_right

-- These produce many non-confluence goals that would be easily solved by better automation.
simp_lc ignore Bool.exists_bool
simp_lc ignore Bool.forall_bool

simp_lc allow ite_eq_left_iff Bool.ite_eq_cond_iff
simp_lc allow ite_eq_right_iff Bool.ite_eq_cond_iff

/-
The actual checks happen in `tests/lean/000_simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in _root_ Bool
