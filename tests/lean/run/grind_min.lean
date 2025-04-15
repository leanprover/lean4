set_option grind.warning false

example (as : Array α) (lo hi i j : Nat) (h₁ : lo ≤ i) (_ : i < j) (_ : j ≤ hi) (_ : j < as.size)
    (_ : ¬as.size = 0) : min lo (as.size - 1) ≤ i := by
  grind
