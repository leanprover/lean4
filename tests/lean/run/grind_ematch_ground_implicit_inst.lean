set_option grind.warning false

example (a : Nat) : max a a = a := by
  grind

instance : Max Nat where
  max := Nat.max

example (a : Nat) : max a a = a := by
  grind
