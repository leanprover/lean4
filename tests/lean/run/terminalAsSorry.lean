set_option debug.terminalTacticsAsSorry true

example (_ : x > 0) : False := by
  omega

example (_ : x > 0) : False := by
  grind

set_option debug.terminalTacticsAsSorry false

example (_ : x > 0) : False := by
  fail_if_success omega
  sorry

example (_ : x > 0) : False := by
  fail_if_success grind
  sorry
