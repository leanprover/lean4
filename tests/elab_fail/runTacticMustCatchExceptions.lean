example (a b : Nat) : 1 ≤ 2 :=
  have : 1 ≤ a + b := by rfl
  have : a + b ≤ b := by rfl
  have : b ≤ 2     := by rfl
  by decide

example (a b : Nat) : 1 ≤ 2 :=
calc
  1 ≤ a + b := by rfl
  _ ≤ b := by rfl
  _ ≤ 2 := by rfl
