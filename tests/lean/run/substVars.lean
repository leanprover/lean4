example (f : Nat → Nat → Nat) (h₁ : x = 0) (h₂ : y = 0) (h₃ : f 0 0 = 0) : f x y = x := by
  subst_vars
  assumption
