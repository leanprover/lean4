open tactic

set_option pp.binder_types true
set_option pp.implicit true
set_option pp.notation false

example (a : nat) : true :=
by do
  mk_const `add >>= eta_expand >>= trace,
  mk_const `nat.succ >>= eta_expand >>= trace,
  to_expr `(add a) >>= eta_expand >>= trace,
  to_expr `(λ x : nat, add x) >>= eta_expand >>= trace,
  to_expr `(λ x : nat, add x) >>= eta >>= trace,
  to_expr `(add a) >>= eta_expand >>= eta >>= trace,
  constructor
