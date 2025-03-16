set_option grind.warning false

example (a b : Int) (f : Int → Int) (h : a = (if a < 0 then b - 1 else 1 - b)) : False := by
  simp +arith only at h
  guard_hyp h : a = if a + 1 ≤ 0 then b + -1 else -1 * b + 1
  sorry

example {a b : Int} : (if a < b then a else b - 1) ≤ b := by
  grind

example {a b : Int} : (if a < b then a else b - 1) < b := by
  grind

example {a b : Nat} : (if a < b then a else b - 1) ≤ b := by
  grind

example {a b : Nat} : b > 0 → (if a < b then a else b - 1) < b := by
  grind
