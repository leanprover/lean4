@[reducible]
def nat_has_add2 : has_add nat :=
⟨λ x y : nat, nat.add x y⟩

set_option pp.all true

open tactic

example (a b : nat) (H : @add nat (id (id nat.has_add)) a b = @add nat nat_has_add2 a b) : true :=
by do
  s ← simp_lemmas.mk_default,
  get_local `H >>= infer_type >>= s^.dsimplify >>= trace,
  constructor


example (a b : nat) (H : (λ x : nat, @add nat (id (id nat.has_add)) a b) = (λ x : nat, @add nat nat_has_add2 a x)) : true :=
by do
  s ← simp_lemmas.mk_default,
  get_local `H >>= infer_type >>= s^.dsimplify >>= trace,
  constructor

attribute [reducible]
definition nat_has_add3 : nat → has_add nat :=
λ n, has_add.mk (λ x y : nat, x + y)
