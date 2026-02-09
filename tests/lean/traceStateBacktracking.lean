example (h : 0 = 1) : False := by
  first | trace_state; fail | contradiction

example (h : 0 = 1) : False := by
  first | trace "first branch"; fail | contradiction
