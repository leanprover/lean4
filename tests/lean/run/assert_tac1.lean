open tactic

definition tst1 (a : nat) : a = a :=
by do
   assert "x" (expr.const "nat" []),
   trace_state,
   a ← get_local "a",
   exact a,
   x ← get_local "x",
   mk_app ("eq" <.> "refl") [x] >>= exact
