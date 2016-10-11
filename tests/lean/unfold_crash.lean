--
open nat tactic

example (a b : nat) : a = succ b → a = b + 1 :=
by do
  H ← intro `H,
  try (unfold_at [`nat.succ] H),
  unfold [`add], dsimp, unfold [`nat.add],
  trace_state,
  assumption
