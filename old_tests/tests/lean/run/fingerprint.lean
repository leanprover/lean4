open tactic
meta def nat.to_expr (n : nat) : expr := reflect n
run_cmd attribute.fingerprint `reducible >>= trace

definition ex0 : nat :=
by nat.to_expr <$> attribute.fingerprint `reducible >>= exact

attribute [reducible]
definition f : nat := 10

run_cmd attribute.fingerprint `reducible >>= trace

definition ex1 : nat :=
by nat.to_expr <$> attribute.fingerprint `reducible >>= exact

#eval ex1

definition g : nat := 20

run_cmd attribute.fingerprint `reducible >>= trace

definition ex2 : nat :=
by nat.to_expr <$> attribute.fingerprint `reducible >>= exact

#eval ex2

example : ex1 = ex2 :=
rfl

definition h : nat := 20

definition ex3 : nat :=
by nat.to_expr <$> attribute.fingerprint `reducible >>= exact

example : ex1 = ex3 :=
rfl
