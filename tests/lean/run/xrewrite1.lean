import data.nat
open nat tactic

meta_definition xrewrite (th_name : name) : tactic unit :=
do th ← mk_const th_name,
   rewrite_core semireducible tt none ff th,
   try reflexivity

example (a : nat) : (0 + a) + (0 + a) + (0 + a) = a + a + a :=
by xrewrite "zero_add"
