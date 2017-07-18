open tactic bool

example (a b : nat) (H : a + b = 0) : a = a :=
by do
  H ← get_local `H,
  t ← infer_type H,
  trace t,
  set_bool_option `pp.all tt,
  trace "after pp.all true",
  trace t,
  rfl_e ← mk_const `rfl,
  apply rfl_e

#print "set_bool_option tactic does not affect other commands"
#check (0:nat) + 1
