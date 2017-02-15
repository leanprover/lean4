open tactic

definition f (a : nat) := a + 2

attribute [reducible]
definition g (a : nat) := a + 2

example (a : nat) : true :=
by do
  to_expr `(f a) >>= whnf >>= trace,
  to_expr `(g a) >>= whnf >>= trace,
  to_expr `(f a) >>= (λ e, whnf e reducible) >>= trace,
  to_expr `(g a) >>= (λ e, whnf e reducible) >>= trace,
  constructor
