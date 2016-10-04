open tactic

meta def tst (A : Type) : tactic unit :=
do  a ← to_expr `(0),
    v ← eval_expr A a,
    return ()
