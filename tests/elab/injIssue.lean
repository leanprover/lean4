theorem ex1 (n m : Nat) (f : Nat → Nat) : some n = some m → f n = f m := by
  intro h
  injection h with h
  rw [h]
