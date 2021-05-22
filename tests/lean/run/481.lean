example (b : let n : Nat := 2; (n = 13)) : Bool := by
  simp_all

example (b : let n : Nat := 2; (n = 13)) : n + 1 = 14 := by
  simp_all
