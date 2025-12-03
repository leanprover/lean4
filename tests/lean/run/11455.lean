-- Since `by` now has the `arg` precedence, it can be used as an argument directly:

example (a : Nat) : a ≤ a := a.le_of_eq by simp
