open tactic

definition tst2 (a : nat) : a = a :=
by do
   assert "x" (expr.const "nat" []),
   rotate 1,
   trace_state,
   a ← get_local "a",
   mk_app ("eq" <.> "refl") [a] >>= exact,
   a ← get_local "a",
   exact a,
   return ()

print tst2
