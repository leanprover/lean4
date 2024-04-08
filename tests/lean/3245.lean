example (b1 b2 : Bool) :
  (if b1 then 0 else (if b2 then 0 else if b2 then 42 else 0)) = 0 := by
  split
  · rfl
  trace_state
  · split <;> rfl
