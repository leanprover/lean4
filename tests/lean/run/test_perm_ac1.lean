#exit

open expr decidable tactic nat

meta definition is_poly_bin_app : expr → option name
| (app (app (app (app (const op ls) A) s) lhs) rhs) := some op
| _  := none

meta definition is_add (e : expr) : bool  :=
match (is_poly_bin_app e) with
| (some op) := to_bool (op = `add)
| none      := ff
end

meta definition perm_add (e1 e2 : expr) : tactic expr :=
do when (is_add e1 = ff) (fail "given expression is not an addition"),
   add_fn : expr ← return $ app_fn (app_fn e1),
   A      : expr ← return $ app_arg (app_fn add_fn),
   s1     : expr ← mk_app `add_semigroup [A] >>= mk_instance,
   assoc  : expr ← mk_mapp `add.assoc [some A, some s1],
   s2     : expr ← mk_app `add_comm_semigroup [A] >>= mk_instance,
   comm   : expr ← mk_mapp `add.comm [some A, some s2],
   perm_ac add_fn assoc comm e1 e2

meta definition tst_perm : tactic unit :=
do trace "--------",
   (lhs, rhs) ← target >>= match_eq,
   H ← perm_add lhs rhs,
   trace H,
   exact H

set_option trace.tactic.perm_ac true

example (a b c d : nat) : d + b + c + a = a + b + c + d :=
by tst_perm

example (a b c d : nat) : a + b + c + d = d + c + b + a :=
by tst_perm

example (a b c d : nat) : ((b + a) + (d + c)) = (c + d) + (a + b) :=
by tst_perm

example (a b c d e f : nat) : (e + d) + (c + (b + (a + f))) = f + (b + (c + (d + (e + a)))) :=
by tst_perm

example (a b c d e f : nat) : (c + b + a) + (f + (e + d)) = a + b + c + d + e + f :=
by tst_perm

example (a b c d e f : nat) : a + (c + b) + (e + d) + f = f + (b + (c + (d + (e + a)))) :=
by tst_perm

example (a b c d e f : nat) : a + (d + b + c) + (f + e) = a + (b + (c + (d + (e + f)))) :=
by tst_perm
