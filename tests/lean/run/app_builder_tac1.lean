open tactic list nat name option

set_option trace.app_builder true
set_option pp.all true

meta_definition mk_ite (c a b : expr) : tactic expr :=
mk_mapp "ite" [some c, none, none, some a, some b]

example (a b : nat) : nat :=
by do a ← get_local "a",
      b ← get_local "b",
      mk_app "add" [a, b] >>= trace_expr,
      mk_app "mul" [a, b] >>= trace_expr,
      mk_app "sub" [a, b] >>= trace_expr,
      c ← mk_app "eq" [a, b],
      trace_expr c,
      mk_ite c a b >>= trace_expr,
      mk_ite c b a >>= trace_expr,
      assumption,
      return ()
