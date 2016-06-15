open tactic list nat name

set_option trace.app_builder true
set_option pp.all true

example (a b : nat) : nat :=
by do a ← get_local "a",
      b ← get_local "b",
      mk_app "add" [a, b] >>= trace_expr,
      mk_app "mul" [a, b] >>= trace_expr,
      mk_app "sub" [a, b] >>= trace_expr,
      c ← mk_app "eq" [a, b],
      trace_expr c,
      assumption,
      return ()
