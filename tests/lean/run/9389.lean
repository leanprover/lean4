/-! Tests that `zero_mod` is `@[defeq]` -/
example (n : Nat) : 0 % n = 0 := by dsimp
