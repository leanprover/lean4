open tactic

constant foo {A : Type} [inhabited A] (a b : A) : a = default A → a = b

example (a b : nat) : a = 0 → a = b :=
by do
  intro "H",
  apply (expr.const "foo" [level.of_nat 1]),
  trace_state,
  assumption

definition ex : inhabited (nat × nat × bool) :=
by apply_instance

set_option pp.all true
print ex
