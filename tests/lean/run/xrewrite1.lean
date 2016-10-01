open nat tactic
constant zeroadd (a : nat) : 0 + a = a

meta definition xrewrite (th_name : name) : tactic unit :=
do th ← mk_const th_name,
   rewrite_core semireducible tt occurrences.all ff th,
   try reflexivity

example (a : nat) : (0 + a) + (0 + a) + (0 + a) = a + a + a :=
by xrewrite `zeroadd
