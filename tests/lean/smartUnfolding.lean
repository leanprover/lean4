theorem ex1 (x y : Nat) (h : x + 2 = y + 2) : x = y := by
  injection h with h
  trace_state -- without smart unfolding the state would be a mess
  injection h with h
  trace_state -- without smart unfolding the state would be a mess
  assumption
