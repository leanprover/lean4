open tactic

example (a b : nat) : decidable (a = b) :=
by do t ← mk_app `decidable_eq [expr.const `nat []],
      i ← mk_instance t,
      a ← get_local `a,
      b ← get_local `b,
      trace i,
      exact (expr.app_of_list i [a, b])

example (a b : nat) : decidable (a = b) :=
by do t ← target,
      i ← mk_instance t,
      trace i,
      exact i

example (a b : nat) : decidable (a = b) :=
by target >>= mk_instance >>= exact
