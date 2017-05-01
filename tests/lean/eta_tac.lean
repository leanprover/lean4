open tactic

set_option pp.binder_types true
set_option pp.implicit true
set_option pp.notation false

example (a : nat) : true :=
by do
  mk_const `has_add.add >>= head_eta_expand >>= trace,
  mk_const `nat.succ >>= head_eta_expand >>= trace,
  to_expr `(has_add.add a) >>= head_eta_expand >>= trace,
  to_expr `(λ x : nat, has_add.add x) >>= head_eta_expand >>= trace,
  to_expr `(λ x : nat, has_add.add x) >>= head_eta >>= trace,
  to_expr `(has_add.add a) >>= head_eta_expand >>= head_eta >>= trace,
  constructor
