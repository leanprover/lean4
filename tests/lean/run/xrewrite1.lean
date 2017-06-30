open nat tactic
constant zeroadd (a : nat) : 0 + a = a

meta definition xrewrite (th_name : name) : tactic unit :=
do th ← mk_const th_name,
   rewrite_target th,
   try reflexivity

example (a : nat) : (0 + a) + (0 + a) + (0 + a) = a + a + a :=
by xrewrite `zeroadd
