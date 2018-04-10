open tactic

example (a b : nat) (H : a > 0) (H : a > b) (H : b > 0) : a = b → true :=
by do
  a ← get_local `a,
  n ← revert a,
  trace n,
  trace_state,
  intros,
  constructor
