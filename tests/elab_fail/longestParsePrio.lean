syntax "have" ":" term : tactic
example : False := by
  have : True := by simp [  -- should *not* parse the shorter `have` syntax and then fail on `:=`
