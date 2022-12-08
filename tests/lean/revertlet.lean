theorem ex (n : Nat) (h : n = 0) : 0 + n = 0 := by
  let m := n + 1
  let v := m + 1
  have : v = n + 2 := rfl
  trace_state
  subst h
  trace_state
  rfl
