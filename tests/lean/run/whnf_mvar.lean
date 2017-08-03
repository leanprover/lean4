open tactic

example (x : nat) : true :=
by do
  m ← mk_mvar,
  x ← get_local `x,
  unify m x,
  guard (m ≠ x),
  m' ← whnf m,
  guard (m' = x),
  constructor

example (x : nat) : true :=
by do
  m ← mk_mvar,
  z ← to_expr ``(0),
  e ← to_expr ``(@nat.rec (λ _, bool) ff (λ _ _, tt) %%m) tt ff,
  unify m z,
  e' ← whnf e,
  guard (e' = `(ff)),
  constructor
