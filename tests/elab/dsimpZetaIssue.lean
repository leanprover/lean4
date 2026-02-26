example : let x := 0; x + 5 = 5 := by
  dsimp (config := { zeta := false, failIfUnchanged := false })
  trace_state
  simp

example : let x := 0; x + 5 = 5 := by
  dsimp

example : let x := 0; x + y = y := by
  dsimp
  trace_state
  rw [Nat.zero_add]

example : let x := 0; x + y = y := by
  dsimp (config := { zeta := false, failIfUnchanged := false })
  trace_state
  conv => zeta
  trace_state
  rw [Nat.zero_add]
