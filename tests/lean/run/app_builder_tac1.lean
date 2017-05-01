open tactic list nat name

set_option trace.app_builder true
set_option pp.all true

meta definition mk_ite (c a b : expr) : tactic expr :=
mk_mapp `ite [some c, none, none, some a, some b]

example (a b : nat) : nat :=
by do a ← get_local `a,
      b ← get_local `b,
      mk_app `has_add.add [a, b] >>= trace,
      mk_app `has_mul.mul [a, b] >>= trace,
      mk_app `has_sub.sub [a, b] >>= trace,
      c ← mk_app `eq [a, b],
      trace c,
      mk_ite c a b >>= trace,
      mk_ite c b a >>= trace,
      assumption,
      return ()
