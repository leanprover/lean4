/-!
  # `Nat.decidableBallLT` handles large numbers

  `Nat.decidableBallLT` should be performant and not cause
  "maximum recursion depth has been reached" for large numbers. -/

set_option maxRecDepth 512
set_option maxHeartbeats 5000

example : ∀ a < 600, a ^ 2 ≠ 7 := by decide
example : ∀ a ≤ 600, a ^ 2 ≠ 7 := by decide
example : ∀ a : Fin 600, (a : Nat) ^ 2 ≠ 7 := by decide
example : ∃ a < 600, a^2 = 90000 := by decide
example : ∃ a ≤ 600, a^2 = 90000 := by decide
