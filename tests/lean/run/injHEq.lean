example (h : HEq Nat.zero (Nat.succ Nat.zero)) : False := by
  injection h
