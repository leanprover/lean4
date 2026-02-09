open Nat
example : Nat.add zero (succ n) = succ n := by
  unfold Nat.add
  trace_state
  sorry
