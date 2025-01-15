/-!
  # `Nat.decidableBallLT` handles large numbers

  `Nat.decidableBallLT` should be performant and not cause
  "maximum recursion depth has been reached" for large numbers. -/

set_option maxRecDepth 512 in
set_option maxHeartbeats 5000 in
example : ∀ a < 500, a ^ 2 ≠ 7 := by decide
