open tactic

meta def tst1 (A : Type) : tactic unit :=
do  a ← to_expr `(0),
    v ← eval_expr A a,
    return ()

run_command do
  a ← to_expr `(nat.add),
  v ← eval_expr nat a,
  trace v,
  return ()

run_command do
  a ← to_expr `(λ x : nat, x + 1),
  v ← (eval_expr nat a <|> trace "tactic failed" >> return 1),
  trace v,
  return ()
