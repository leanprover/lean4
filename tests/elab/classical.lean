example : Bool := by
  fail_if_success have := ∀ p, decide p -- no classical in scope
  classical
  have := ∀ p, decide p -- uses the classical instance
  guard_expr decide (0 < 1) = @decide (0 < 1) (Nat.decLt 0 1)
  exact decide (0 < 1) -- will use the decidable instance

-- double check no leakage
example : Bool := by
  fail_if_success have := ∀ p, decide p -- no classical in scope
  exact decide (0 < 1) -- uses the decidable instance

-- check that classical respects tactic blocks
example : Bool := by
  fail_if_success have := ∀ p, decide p -- no classical in scope
  ( -- start a scope
    classical
    have := ∀ p, decide p -- uses the classical instance
  )
  fail_if_success have := ∀ p, decide p -- no classical in scope again
  exact decide (0 < 1) -- will use the decidable instance
