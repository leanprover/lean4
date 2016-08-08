import algebra.group data.nat

open expr decidable tactic nat

meta_definition is_poly_bin_app : expr → option name
| (app (app (app (app (const op ls) A) s) lhs) rhs) := some op
| _  := none

meta_definition is_add (e : expr) : bool  :=
match (is_poly_bin_app e) with
| (some op) := to_bool (op = `add)
| none      := ff
end

meta_definition flat_add (e : expr) : tactic (expr × expr) :=
do when (is_add e = ff) (fail "given expression is not an addition"),
   add_fn : expr ← return $ app_fn (app_fn e),
   A      : expr ← return $ app_arg (app_fn add_fn),
   s      : expr ← mk_app `add_semigroup [A] >>= mk_instance,
   assoc  : expr ← mk_mapp `add.assoc [some A, some s],
   flat_assoc add_fn assoc e

meta_definition tst_flat_add : tactic unit :=
do trace "--------",
   (lhs, rhs) ← target >>= match_eq,
   (new_lhs, H) ← flat_add lhs,
   trace H,
   exact H

example (a b c d : nat) : a + b + c + d = a + (b + (c + d)) :=
by tst_flat_add

example (a b c d : nat) : a + (b + (c + d)) = a + (b + (c + d)) :=
by tst_flat_add

example (a b c d : nat) : ((a + b) + (c + d)) = a + (b + (c + d)) :=
by tst_flat_add

example (a b c d e f : nat) : (a + b) + (c + (d + (e + f))) = a + (b + (c + (d + (e + f)))) :=
by tst_flat_add

example (a b c d e f : nat) : (a + b + c) + (d + (e + f)) = a + (b + (c + (d + (e + f)))) :=
by tst_flat_add

example (a b c d e f : nat) : a + b + c + d + e + f = a + (b + (c + (d + (e + f)))) :=
by tst_flat_add

example (a b c d e f : nat) : a + (b + c) + (d + e) + f = a + (b + (c + (d + (e + f)))) :=
by tst_flat_add

example (a b c d e f : nat) : a + (b + c + d) + (e + f) = a + (b + (c + (d + (e + f)))) :=
by tst_flat_add

example (a b c d e f : nat) : a + (b + (c + d)) + (e + f) = a + (b + (c + (d + (e + f)))) :=
by tst_flat_add

example (a b c d e f : nat) : (a + b) + (c + d) + (e + f) = a + (b + (c + (d + (e + f)))) :=
by tst_flat_add
