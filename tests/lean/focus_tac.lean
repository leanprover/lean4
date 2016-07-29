open tactic

example (a : nat) : a = a :=
by do
   define `x (expr.const `nat []),
   trace "---- after assert ----",
   trace_state,
   solve1 (do trace "--- inside focus tac ---", trace_state), -- SHOULD FAIL HERE
   trace "---- after focus tac ----",
   trace_state,
   x ← get_local `x,
   mk_app `eq.refl [x] >>= exact,
   return ()


definition tst2 (a : nat) : a = a :=
by do
   define `x (expr.const `nat []),
   trace "---- after assert ----",
   trace_state,
   solve1 (do trace "--- inside focus tac ---", trace_state, assumption),
   trace "---- after focus tac ----",
   trace_state,
   x ← get_local `x,
   mk_app `eq.refl [x] >>= exact,
   return ()
