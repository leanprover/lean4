/-! This test ensures that local declarations explicitly passed to `grind` produce an appropriate
    error message, instead of just `unknown constant '...'`. -/

/-- error: redundant parameter `h`, `grind` uses local hypotheses automatically -/
#guard_msgs in
example : 0 = 0 := by
  have h : 1 = 1 := rfl
  grind [h]

/-- error: redundant parameter `h`, `grind` uses local hypotheses automatically -/
#guard_msgs in
example : 0 = 0 := by
  have h : 1 = 1 := rfl
  grind only [h]

-- example : 0 = 1 := by
--   have h : 0 = 1 := sorry
--   grind [- h]
