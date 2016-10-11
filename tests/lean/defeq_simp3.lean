attribute [reducible]
definition nat_has_add2 : has_add nat :=
has_add.mk (λ x y : nat, x + y)

attribute [reducible]
definition nat_has_add3 : nat → has_add nat :=
λ n, has_add.mk (λ x y : nat, x + y)

open tactic
set_option pp.all true

example (a b : nat) (H : (λ x : nat, @add nat nat_has_add2 a x) = (λ x : nat, @add nat (nat_has_add3 x) a b)) : true :=
by do
  s ← simp_lemmas.mk_default,
  get_local `H >>= infer_type >>= s^.dsimplify >>= trace,
  constructor
