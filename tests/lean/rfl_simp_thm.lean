def inc (x : Nat) := x + 1

@[simp] theorem inc_eq : inc x = x + 1 := rfl

theorem ex (a b : Fin (inc n)) (h : a = b) : b = a := by
  simp +implicitDefEqProofs only [inc_eq] at a
  trace_state
  exact h.symm
