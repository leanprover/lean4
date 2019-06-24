def foo (xs : List Nat) :=
xs.span (λ n, coe (decide (n = 1)))
