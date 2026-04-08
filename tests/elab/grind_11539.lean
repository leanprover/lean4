example {n a b : Nat}
  (this : (b : Int) ^ (n + 1) + ↑(n + 1) * ↑b ^ (n + 1 - 1) * (↑a - ↑b) ≤
          (↑b + (↑a - ↑b)) ^ (n + 1)) :
    (n + 1) * a * b ^ n ≤ a ^ (n + 1) + n * b * b ^ n := by
grind (splits := 0)

example {n a b : Nat}
  (this : (b : Int) ^ (n + 1) + ↑(n + 1) * ↑b ^ (n + 1 - 1) * (↑a - ↑b) ≤
          (↑b + (↑a - ↑b)) ^ (n + 1)) :
    (n + 1) * a * b ^ n ≤ a ^ (n + 1) + n * b * b ^ n := by
grind
