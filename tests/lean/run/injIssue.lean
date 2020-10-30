theorem ex1 (n m : Nat) : some n = some m → n = m := by
  intro h
  injection h with h
  exact h
