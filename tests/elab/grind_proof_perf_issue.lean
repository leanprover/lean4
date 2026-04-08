example {n : Nat} (hn : 500000 ≤ n) (hn' : n ≤ 2000000) : n - 500000 ≥ 1500001 → False := by
  grind

example {n : Nat} (hn : 57343 < n) (hn' : n < 1114112) :
    n - (57343 + 1) < 1114111 - 57343 := by
  grind
