attribute [reducible]
definition nat_has_add2 : has_add nat :=
has_add.mk (λ x y : nat, x + y)

attribute [reducible]
definition nat_has_add3 : nat → has_add nat :=
λ n, has_add.mk (λ x y : nat, x + y)

open tactic
set_option pp.all true

-- Example where instance canonization does not work.
-- Remark: we can "fix" it by re-running defeq_simp until there is no change.
-- However, this is too expensive. Well, if users want they can define their own defeq_simp that implements this
-- behavior.
example (a b : nat) (H : (λ x : nat, @has_add.add nat (nat_has_add3 x) a b) = (λ x : nat, @has_add.add nat nat_has_add2 a x)) : true :=
by do
  s ← simp_lemmas.mk_default,
  e ← get_local `H >>= infer_type, s^.dsimplify e {fail_if_unchaged := ff} >>= trace,
  trace "---------",
  -- The following should work
  e ← get_local `H >>= infer_type,
  e ← s^.dsimplify e {fail_if_unchaged := ff},
  s^.dsimplify e {fail_if_unchaged := ff} >>= trace,
  constructor
