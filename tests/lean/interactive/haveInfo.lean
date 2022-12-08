example : False := by
  have : True := by
    skip
  --^ $/lean/plainGoal
    skip
  admit

example : False := by
  have : True := by
               --^ $/lean/plainGoal
    skip
    skip
  admit

example : False := by
  have : True := by
               --^ $/lean/plainGoal
    skip
    skip
  admit

example : False := by
  have : True := by
    skip
--^ $/lean/plainGoal
    skip
  admit
