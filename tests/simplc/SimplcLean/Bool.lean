import SimplcLean._root_

simp_lc whitelist Bool.bne_assoc Bool.bne_self_left -- `(x != (y != (x != (y != b)))) = b` `(y != (x != y)) = x`

#guard_msgs (drop info) in
simp_lc check in Bool

-- x y : Bool
-- ⊢ x = (y != (x != y))
simp_lc whitelist bne_self_eq_false Bool.bne_assoc

-- I'd expected that making `Decidable.em` a `@[simp]` would help here, but it doesn't seem to.
-- w : Decidable p
-- ⊢ p ∨ ¬p
simp_lc whitelist ite_else_decide_not_self Bool.if_true_left
-- w : Decidable p
-- ⊢ ¬p ∨ p
simp_lc whitelist ite_then_decide_self Bool.if_true_right

-- These produce many non-confluence goals that would be easily solved by better automation.
simp_lc ignore Bool.exists_bool
simp_lc ignore Bool.forall_bool

simp_lc whitelist ite_eq_left_iff Bool.ite_eq_cond_iff
simp_lc whitelist ite_eq_right_iff Bool.ite_eq_cond_iff

#guard_msgs (drop info) in
simp_lc check in _root_ Bool
