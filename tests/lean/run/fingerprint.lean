open tactic

run_command attribute.fingerprint `reducible >>= trace

definition ex0 : nat :=
by attribute.fingerprint `reducible >>= expr_of_nat >>= exact

attribute [reducible]
definition f : nat := 10

run_command attribute.fingerprint `reducible >>= trace

definition ex1 : nat :=
by attribute.fingerprint `reducible >>= expr_of_nat >>= exact

vm_eval ex1

definition g : nat := 20

run_command attribute.fingerprint `reducible >>= trace

definition ex2 : nat :=
by attribute.fingerprint `reducible >>= expr_of_nat >>= exact

vm_eval ex2

example : ex1 = ex2 :=
rfl

definition h : nat := 20

definition ex3 : nat :=
by attribute.fingerprint `reducible >>= expr_of_nat >>= exact

example : ex1 = ex3 :=
rfl
