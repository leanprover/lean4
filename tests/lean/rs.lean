rewrite_set S
variable bracket : Type → Bool
axiom bracket_eq (a : Bool) : bracket a = a
add_rewrite bracket_eq : S
add_rewrite and_truer and_comm not_true not_neq not_and exists_or_distribute exists_and_distributel : S
add_rewrite exists_rem eq_id forall_rem : S
add_rewrite Nat::add_zeror Nat::add_comm Nat::add_assoc Nat::mul_comm not_true not_false : S
print rewrite_set S