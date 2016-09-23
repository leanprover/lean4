attribute [reducible]
definition nat_has_add2 : has_add nat :=
has_add.mk (λ x y : nat, x + y)

set_option pp.all true
-- set_option trace.defeq_simplifier true

open tactic

example (a b : nat) (H : @add nat (id (id nat.has_add)) a b = @add nat nat_has_add2 a b) : true :=
by do
  get_local `H >>= infer_type >>= defeq_simp >>= trace,
  constructor

constant x1 : nat -- update the environment to force defeq_canonize cache to be reset

example (a b : nat) (H : (λ x : nat, @add nat (id (id nat.has_add)) a b) = (λ x : nat, @add nat nat_has_add2 a x)) : true :=
by do
  get_local `H >>= infer_type >>= defeq_simp >>= trace,
  constructor

attribute [reducible]
definition nat_has_add3 : nat → has_add nat :=
λ n, has_add.mk (λ x y : nat, x + y)

constant x2 : nat -- update the environment to force defeq_canonize cache to be reset

example (a b : nat) (H : (λ x : nat, @add nat nat_has_add2 a x) = (λ x : nat, @add nat (nat_has_add3 x) a b)) : true :=
by do
  get_local `H >>= infer_type >>= defeq_simp >>= trace,
  constructor

constant x3 : nat

-- Example where instance canonization does not work.
-- Remark: we can "fix" it by re-running defeq_simp until there is no change.
-- However, this is too expensive. Well, if users want they can define their own defeq_simp that implements this
-- behavior.
example (a b : nat) (H : (λ x : nat, @add nat (nat_has_add3 x) a b) = (λ x : nat, @add nat nat_has_add2 a x)) : true :=
by do
  get_local `H >>= infer_type >>= defeq_simp >>= trace,
  trace "---------",
  -- The following should work
  get_local `H >>= infer_type >>= defeq_simp >>= defeq_simp >>= trace,
  constructor

constant x4 : nat -- update the environment to force defeq_canonize cache to be reset

-- Example where instance canonization does not work.
-- This is a different issue. We can only make them work if we normalize (nat_has_add3 x) and (nat_has_add3 y).
-- Again, the user can workaround it by manually normalizing these instances before invoking defeq_simp.
example (a b : nat)
        (H : (λ x y : nat, @add nat (nat_has_add3 x) a b) =
             (λ x y : nat, @add nat (nat_has_add3 y) a x)) : true :=
by do
  get_local `H >>= infer_type >>= defeq_simp >>= trace,
  constructor
