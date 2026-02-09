example {k : Nat} (h : k - 1 + 1 = k) :
    2 ^ (k - 1 + 1) = 2 ^ k := by
  grind

example (h : a = b + c) : 2 ^ a = 2^b * 2^c := by
  grind

example (h : a = c + b) : 2 ^ a = 2^b * 2^c := by
  grind

example (h : a = 1 + b) : 2 ^ a = 2^b * 2 := by
  grind
