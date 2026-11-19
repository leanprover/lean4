example : True := by
  fail_if_success (have : False := by assumption)
  trivial

example : True := by
  have : False := by
    fail_if_success assumption
    sorry
  trivial
