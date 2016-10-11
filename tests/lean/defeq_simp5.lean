attribute [reducible]
definition nat_has_add2 : has_add nat :=
has_add.mk (λ x y : nat, x + y)

attribute [reducible]
definition nat_has_add3 : nat → has_add nat :=
λ n, has_add.mk (λ x y : nat, x + y)

open tactic
set_option pp.all true

-- Example where instance canonization does not work.
-- This is a different issue. We can only make them work if we normalize (nat_has_add3 x) and (nat_has_add3 y).
-- Again, the user can workaround it by manually normalizing these instances before invoking defeq_simp.
example (a b : nat)
        (H : (λ x y : nat, @add nat (nat_has_add3 x) a b) =
             (λ x y : nat, @add nat (nat_has_add3 y) a x)) : true :=
by do
  s ← simp_lemmas.mk_default,
  get_local `H >>= infer_type >>= s^.dsimplify >>= trace,
  constructor
