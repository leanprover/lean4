example {n : Nat} (hn : 500000 ≤ n) (hn' : n ≤ 2000000) : n - 500000 ≥ 1500001 → False := by
  grind
