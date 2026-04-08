example : True := by
  unfold Nat.add

example (h : x = 2 * y) : True := by
  unfold Nat.add at h
