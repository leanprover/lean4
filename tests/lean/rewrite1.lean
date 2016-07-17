import data.nat
open nat tactic

example (a b : nat) : a * 0 + 0 + b + 0 = b :=
by do
 rewrite "mul_zero",
 trace_state,
 rewrite "add_zero",
 repeat $ rewrite "zero_add"

print "---------"

example (a b : nat) (H : a + b * 0 + 0 = b) : b = a :=
by do
 rewrite_at "mul_zero" "H",
 trace_state,
 rewrite_at "add_zero" "H",
 rewrite_at "add_zero" "H",
 symmetry,
 assumption

print "---------"

example (a : nat) : (0 + a) + (0 + a) + (0 + a) = a + a + a :=
by rewrite "zero_add"

meta_definition rewrite_occs (th_name : name) (occs : list nat) : tactic unit :=
do th ← mk_const th_name,
   rewrite_core reducible tt (some occs) ff th,
   try reflexivity

print "---------"

example (a : nat) : (0 + a) + (0 + a) + (0 + a) = a + a + a :=
by do
   rewrite_occs "zero_add" [1, 3],
   trace_state,
   rewrite "zero_add"

print "---------"

example (a : nat) : (0 + a) + (0 + a) + (0 + a) = a + a + a :=
by do
   rewrite_occs "zero_add" [2],
   trace_state,
   rewrite_occs "zero_add" [2],
   trace_state,
   rewrite "zero_add"
