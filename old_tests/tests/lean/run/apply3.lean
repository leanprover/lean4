open tactic

#print "------- fapply version ----------"

example (a : nat) : ∃ x : nat, x = a :=
by do
  c₁ ← return (expr.const `Exists.intro [level.of_nat 1]),
  fapply c₁, /- fapply adds all unassigned variables -/
  trace_state,
  swap, /- swap witness and ?M = a -/
  a ← get_local `a,
  mk_app `eq.refl [a] >>= exact

#print "------- apply version ----------"

example (a : nat) : ∃ x : nat, x = a :=
by do
  c₁ ← return (expr.const `Exists.intro [level.of_nat 1]),
  /- apply does not add the goal |- nat -/
  apply c₁,
  trace_state,
  a ← get_local `a,
  mk_app `eq.refl [a] >>= exact
