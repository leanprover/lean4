open tactic list

meta definition foo (a : pexpr) : pexpr :=
`(%%a + %%a + %%a + b)

example (a b : nat) : a = a :=
by do
   a ← get_local `a,
   t1 ← mk_app `add [a, a],
   t2 ← to_expr (foo (to_pexpr t1)),
   trace t2,
   r ← mk_app (`eq.refl) [a],
   exact r
