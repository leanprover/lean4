import Lean.SimpLC.Whitelists.List
import Lean.SimpLC.Whitelists.Bool
import Lean.SimpLC.Whitelists.Nat

-- TODO: re-evaluate these (appeared while moving `SimpLC` into Lean.)
simp_lc whitelist exists_eq Sum.exists
simp_lc whitelist exists_eq_left Sum.exists
simp_lc whitelist exists_eq_right Sum.exists
simp_lc whitelist exists_and_left Sum.exists
simp_lc whitelist exists_and_right Sum.exists
simp_lc whitelist exists_eq_left' Sum.exists
simp_lc whitelist exists_eq_right' Sum.exists
simp_lc whitelist exists_eq_right_right Sum.exists
simp_lc whitelist exists_eq_right_right' Sum.exists
simp_lc whitelist exists_or_eq_left Sum.exists
simp_lc whitelist exists_or_eq_left' Sum.exists
simp_lc whitelist exists_or_eq_right' Sum.exists
simp_lc whitelist Sum.exists exists_const
simp_lc whitelist Sum.exists exists_eq_or_imp
simp_lc whitelist Sum.exists exists_or_eq_right
simp_lc whitelist Sum.exists exists_apply_eq_apply
simp_lc whitelist Sum.exists exists_eq'
simp_lc whitelist forall_const Sum.forall
simp_lc whitelist forall_eq Sum.forall
simp_lc whitelist forall_eq' Sum.forall
simp_lc whitelist forall_eq_or_imp Sum.forall
simp_lc whitelist forall_eq_apply_imp_iff Sum.forall
simp_lc whitelist Sum.forall forall_apply_eq_imp_iff
simp_lc whitelist Sum.forall forall_apply_eq_imp_iff₂
simp_lc whitelist Sum.getLeft_eq_iff eq_iff_iff
simp_lc whitelist Sum.getLeft_eq_iff List.ne_cons_self
simp_lc whitelist Sum.getLeft_eq_iff List.self_eq_append_right
simp_lc whitelist Sum.getLeft_eq_iff Nat.self_eq_add_left
simp_lc whitelist Sum.getLeft_eq_iff Bool.eq_not_self
simp_lc whitelist Sum.getLeft_eq_iff Bool.iff_self_or
simp_lc whitelist Sum.getRight_eq_iff eq_iff_iff
simp_lc whitelist Sum.getRight_eq_iff List.ne_cons_self
simp_lc whitelist Sum.getRight_eq_iff List.self_eq_append_right
simp_lc whitelist Sum.getRight_eq_iff Nat.self_eq_add_left
simp_lc whitelist Sum.getRight_eq_iff Bool.eq_not_self
simp_lc whitelist Sum.getRight_eq_iff Bool.iff_self_or
simp_lc whitelist List.self_eq_append_left Sum.getLeft_eq_iff
simp_lc whitelist List.self_eq_append_left Sum.getRight_eq_iff
simp_lc whitelist Nat.self_eq_add_right Sum.getLeft_eq_iff
simp_lc whitelist Nat.self_eq_add_right Sum.getRight_eq_iff
simp_lc whitelist Bool.iff_self_and Sum.getLeft_eq_iff
simp_lc whitelist Bool.iff_self_and Sum.getRight_eq_iff
simp_lc whitelist Bool.iff_and_self Sum.getLeft_eq_iff
simp_lc whitelist Bool.iff_and_self Sum.getRight_eq_iff
simp_lc whitelist Bool.iff_and_not_self Sum.getLeft_eq_iff
simp_lc whitelist Bool.iff_and_not_self Sum.getRight_eq_iff
simp_lc whitelist Bool.iff_not_self_and Sum.getLeft_eq_iff
simp_lc whitelist Bool.iff_not_self_and Sum.getRight_eq_iff
simp_lc whitelist Bool.iff_or_self Sum.getLeft_eq_iff
simp_lc whitelist Bool.iff_or_self Sum.getRight_eq_iff
simp_lc whitelist Bool.iff_or_not_self Sum.getLeft_eq_iff
simp_lc whitelist Bool.iff_or_not_self Sum.getRight_eq_iff
simp_lc whitelist Bool.iff_not_self_or Sum.getLeft_eq_iff
simp_lc whitelist Bool.iff_not_self_or Sum.getRight_eq_iff

/-
The actual checks happen in `tests/lean/run/simplc.lean`.
This commented out command remains here for convenience while debugging.
-/
-- #guard_msgs (drop info) in
-- simp_lc check in Sum List Bool Nat _root_
