set_option grind.warning false

example (x : Nat) : x ≥ (0 : Int) := by grind
example (x : Nat) : Int.ofNat x ≥ (0 : Int) := by grind
example (x : Nat) : NatCast.natCast x ≥ 0 := by grind
example (x : Nat) : x ≥ (-1 : Int) := by grind
example (x : Nat) : Int.ofNat x ≥ (-1 : Int) := by grind
example (x : Nat) : NatCast.natCast x ≥ -1 := by grind
