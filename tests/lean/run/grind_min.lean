set_option grind.warning false
reset_grind_attrs%
attribute [grind =] Nat.min_def -- This annotation should eventually be in the Std library

example (as : Array α) (lo hi i j : Nat) (h₁ : lo ≤ i) (_ : i < j) (_ : j ≤ hi) (_ : j < as.size)
    (_ : ¬as.size = 0) : min lo (as.size - 1) ≤ i := by
  grind
