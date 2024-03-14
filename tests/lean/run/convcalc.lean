example (P : Nat → Prop) (h : P 4) : P ((1 + 1) + 2) := by
  conv => arg 1; calc
    (1 + 1) + 2
    _ = 2 + 2 := by simp
    _ = 4 := by simp
  exact h
