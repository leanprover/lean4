open tactic

meta def check_expr (p : pexpr) (t : expr) : tactic unit :=
do e ← to_expr p, guard (t = e)

example : true :=
let x := 10 in
by do h ← get_local `x,
      head_zeta h >>= check_expr `(10),
      triv

example : let x := 10 in true :=
by do x ← intro1,
      head_zeta x >>= check_expr `(10),
      triv

example : true :=
by do h ← to_expr `((λ x : nat, x + 1) 1),
      head_beta h >>= check_expr `(1 + 1),
      triv
