set_option maxRecDepth 1024 -- TODO: investigate why we had to increase it
example (a : Nat) : ((2 ^ 7) + a) - 2 ^ 7 = 0 := by
  generalize 0 - 0 = x
  sorry
