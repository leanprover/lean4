module
example (x : Nat) : x ≥ (0 : Int) := by grind
example (x : Nat) : Int.ofNat x ≥ (0 : Int) := by grind
example (x : Nat) : NatCast.natCast x ≥ 0 := by grind
example (x : Nat) : x ≥ (-1 : Int) := by grind
example (x : Nat) : Int.ofNat x ≥ (-1 : Int) := by grind
example (x : Nat) : NatCast.natCast x ≥ -1 := by grind

example (n : Nat) : Nat.cast n = n := by
  grind

example (n m a : Nat) : n = m → Nat.cast n - a = m - a := by
  grind
