open tactic

example (a b c : nat) : a = b → c = b → a = c :=
by do
  h ← intro `h,
    --^ "command": "info"
  intros,
  transitivity,
--^ "command": "info"
  trace_state,
  assumption,
--^ "command": "info"
  symmetry,
--^ "command": "info"
  assumption
--^ "command": "info"
