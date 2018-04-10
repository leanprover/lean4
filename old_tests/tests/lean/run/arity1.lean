open tactic decidable

definition foo (A B : Type) := A → B

definition boo (c : bool) :=
cond c nat bool

definition bla (a : nat) : boo (to_bool (a > 0)) → foo nat nat :=
λ v x, a + x

example : true :=
by do
  bla ← mk_const `bla,
  infer_type bla >>= trace,
  n   ← get_arity bla,
  trace ("n arity: " ++ to_string n),
  when (n ≠ 3) (fail "bla is expected to have arity 3"),
  constructor
