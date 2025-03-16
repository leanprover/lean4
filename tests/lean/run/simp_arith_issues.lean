example (a b : Int) (f : Int → Int) (h : a = (if a < 0 then b - 1 else 1 - b)) : False := by
  simp +arith only at h
  guard_hyp h : a = if a + 1 ≤ 0 then b + -1 else -1 * b + 1
  sorry
