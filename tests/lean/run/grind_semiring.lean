example (n t : Nat) : 1 ^ (n / 3) * 2 ^ t = 2 ^ t := by grind

example (n t : Nat) : (1 : Int) ^ (n / 3) * 2 ^ t = 2 ^ t := by grind
