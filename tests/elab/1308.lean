@[default_instance high] instance : HPow R Nat R where hPow a _ := a
example (x y : Nat) : (x + y) ^ 3 = x ^ 3 + y ^ 3 + 3 * (x * y ^ 2 + x ^ 2 * y) := sorry
