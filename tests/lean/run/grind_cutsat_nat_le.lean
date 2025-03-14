theorem ex1 (x y z : Nat) : x < y + z → y + 1 < z → z + x < 3*z := by
  grind


theorem ex2 (x y z : Nat) : x < y + z → y + 1 < z → (p ↔ z + x < 3*z) → p := by
  grind

#print ex1
#print ex2
