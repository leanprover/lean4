def f (n : Nat) := n + 1
example (k : Nat) : let x := 10; f x = k := by
  have : f 10 = 11 := rfl
  intro x
  rw [this]
  trace_state
  revert x
  trace_state
  sorry
