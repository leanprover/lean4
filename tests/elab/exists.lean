example : ∃ x : Nat, x = x := by
  exists 0

example : ∃ x : Nat, ∃ y : Nat, x > y := by
  exists 1, 0

example : (x : Nat) ×' (y : Nat) ×' x > y := by
  exists 1, 0

example : { x : Nat // x > 2 } := by
  exists 3
