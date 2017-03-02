open tactic

set_option pp.binder_types true
set_option pp.implicit true
set_option pp.notation false

example (a : nat) : true :=
by do
  mk_const `add >>= head_eta_expand >>= trace,
  mk_const `nat.succ >>= head_eta_expand >>= trace,
  to_expr `(add a) >>= head_eta_expand >>= trace,
  to_expr `(λ x : nat, add x) >>= head_eta_expand >>= trace,
  to_expr `(λ x : nat, add x) >>= head_eta >>= trace,
  to_expr `(add a) >>= head_eta_expand >>= head_eta >>= trace,
  constructor
