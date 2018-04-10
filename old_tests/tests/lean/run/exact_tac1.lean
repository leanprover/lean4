open tactic list

example (a b : nat) : a = a :=
by do
  a ← get_local `a,
  r ← mk_app `eq.refl [a],
  exact r

set_option pp.all true

example (a b : nat) (f : nat → nat) : a = b → f a = f b :=
by do
  intro `H,
  H ← get_local `H,
  f ← get_local `f,
  r ← mk_app `congr_arg [f, H],
  trace r,
  exact r
