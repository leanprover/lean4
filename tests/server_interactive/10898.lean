/-!
# `rw .. at *` should save metacontext
-/

example (h : 1 + 2 = 3) : True := by
  rewrite [Nat.add_comm _] at *
                      --^ $/lean/plainGoal
                      --^ $/lean/plainTermGoal
  trivial
