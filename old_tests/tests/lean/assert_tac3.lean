open tactic

definition tst2 (a : nat) : a = a :=
by do
   define `x (expr.const `nat []),
   rotate 1,
   trace_state,
   a ← get_local `a,
   mk_app `eq.refl [a] >>= exact,
   a ← get_local `a,
   exact a,
   return ()

#print tst2

definition tst3 (a b : nat) : a = a :=
by do
   define `x (expr.const `nat []),
   rotate 1,
   trace_state,
   x ← get_local `x,
   mk_app `eq.refl [x] >>= exact,
   trace "-- second goal was indirectly solved by the previous tactic",
   trace_state,
   return ()
