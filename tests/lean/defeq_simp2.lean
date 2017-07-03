open tactic

constant f (n : nat) : n ≥ 0 → nat

axiom foo1 (n : nat) : n ≥ 0
axiom foo2 (n : nat) : n ≥ 0
axiom foo3 (n : nat) : n ≥ 0

  -- by default we dont canonize proofs
example (a b : nat) (H : f a (foo1 a) = f a (foo2 a)) : true :=
by do
  s ← simp_lemmas.mk_default,
  e ← get_local `H >>= infer_type, s^.dsimplify [] e {fail_if_unchanged := ff} >>= trace,
  constructor

constant x1 : nat -- update the environment to force defeq_canonize cache to be reset

example (a b : nat) (H : f a (foo1 a) = f a (foo2 a)) : true :=
by do
  s ← simp_lemmas.mk_default,
  e ← get_local `H >>= infer_type, s^.dsimplify [] e {fail_if_unchanged := ff} >>= trace,
  constructor

constant x2 : nat -- update the environment to force defeq_canonize cache to be reset

example (a b : nat) (H : f a (id (id (id (foo1 a)))) = f a (foo2 a)) : true :=
by do
  s ← simp_lemmas.mk_default,
  get_local `H >>= infer_type >>= s^.dsimplify >>= trace,
  constructor

-- Example that does not work
example (a b : nat) (H : (λ x, f x (id (id (id (foo1 x))))) = (λ x, f x (foo2 x))) : true :=
by do
  s ← simp_lemmas.mk_default,
  get_local `H >>= infer_type >>= s^.dsimplify >>= trace,
  constructor
