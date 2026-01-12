example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = a * b := by grind

example {a b : Nat} (ha : 1 ≤ a) : (a - 1 + 1) * b = a * b := by
  grind => done
