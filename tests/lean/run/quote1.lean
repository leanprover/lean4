open tactic list

meta_definition foo (a : qexpr) : qexpr :=
`(%%a + %%a + %%a + b)

example (a b : nat) : a = a :=
by do
   a ← get_local "a",
   t1 ← mk_app "add" [a, a],
   t2 ← to_expr (foo (to_qexpr t1)),
   trace t2,
   r ← mk_app ("eq" <.> "refl") [a],
   exact r
