meta def mk_cycle : tactic unit :=
do [g] <- tactic.get_goals,
   tactic.refine (pexpr.of_expr g)

example : true :=
by mk_cycle

meta def mk_cycle2 : tactic unit :=
do [g] <- tactic.get_goals,
   tactic.exact g

example : true :=
by mk_cycle2

meta def mk_cycle3 : tactic unit :=
do [g] <- tactic.get_goals,
   tactic.refine ``(id %%g)

example : true :=
by mk_cycle3
