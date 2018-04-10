open tactic

set_option pp.all true

meta example (m1 : tactic nat) (m2 : nat → tactic bool) : true :=
by do
  m1 ← get_local `m1,
  m2 ← get_local `m2,
  b  ← mk_app `has_bind.bind [m1, m2],
  trace b,
  constructor
