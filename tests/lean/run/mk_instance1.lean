open tactic

example (a b : nat) : decidable (a = b) :=
by do t ← mk_app "decidable_eq" [expr.const "nat" []],
      i ← mk_instance t,
      a ← get_local "a",
      b ← get_local "b",
      trace_expr i,
      exact (expr.app (expr.app i a) b)

example (a b : nat) : decidable (a = b) :=
by do t ← target,
      i ← mk_instance t,
      trace_expr i,
      exact i

example (a b : nat) : decidable (a = b) :=
by target >>= mk_instance >>= exact
