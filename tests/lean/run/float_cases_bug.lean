def foo (xs : List Nat) :=
xs.span (λ n, ↑(decide (n = 1)))
