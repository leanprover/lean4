instance : HPow Rat Rat Rat := sorry

example (b p : Rat) (_ : 0 < b^p) (_ : ¬ 0 ≤ b^p) : False := by
  grind

example (b : Rat) (n : Nat) (_ : 0 < b^n) (_ : ¬ 0 ≤ b^n) : False := by
  grind -- this one also used to fai
