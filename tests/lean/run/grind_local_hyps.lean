/-! This test ensures that local declarations explicitly passed to `grind` produce an appropriate
    error message, instead of just `unknown constant '...'`. -/

-- Checks that (invalid) identifiers which are not local declarations are still elaborated as global
-- constants.
/-- error: unknown constant 'h' -/
#guard_msgs in
example : 0 = 0 := by
  grind [h]

-- Checks that local hypotheses do not shadow global constants.
def P := 0 = 0
example : 0 = 0 := by
  have P : 0 = 0 := rfl
  grind [P]

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
