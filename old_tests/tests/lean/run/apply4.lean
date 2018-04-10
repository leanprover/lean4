open tactic bool
universe variables u
constant foo {A : Type u} [inhabited A] (a b : A) : a = default A → a = b

example (a b : nat) : a = 0 → a = b :=
by do
  intro `H,
  apply (expr.const `foo [level.of_nat 0]),
  trace_state,
  assumption

definition ex : inhabited (nat × nat × bool) :=
by apply_instance

set_option pp.all true
#print ex

set_option pp.all false

example (a b : nat) : a = 0 → a = b :=
by do
  intro `H,
  apply_core (expr.const `foo [level.of_nat 0]) {approx := ff, new_goals := new_goals.all, instances := ff },
  trace_state,
  a ← get_local `a,
  trace_state,
  mk_app `inhabited.mk [a] >>= exact,
  trace "--------",
  trace_state,
  reflexivity

#print "----------------"
set_option pp.all true

example (a b : nat) : a = 0 → a = b :=
by do
  intro `H,
  foo ← mk_const `foo,
  trace foo,
  apply foo,
  trace_state,
  assumption


example (a b : nat) : a = 0 → a = b :=
by do
  `[intro],
  apply_core (expr.const `foo [level.of_nat 0]) {approx := ff, new_goals := new_goals.all, instances := ff},
  `[exact inhabited.mk a],
  reflexivity
