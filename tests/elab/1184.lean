@[simp] theorem one_le_of_lt (h: n < m) : 1 ≤ m := Nat.lt_of_le_of_lt (Nat.zero_le _) h

example (h: n < m) : 1 ≤ m := by
  simp (disch := assumption) [h]
