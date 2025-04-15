set_option grind.warning false

example (a b : Nat) : a  = a + b - b := by
  grind

example (a b : Int) : a = a + b - b := by
  grind

example (a b : Nat) : a = a + 2^b - 2^b := by
  grind

example (a b : Nat) : 2^a = 2^a + b - b := by
  grind
