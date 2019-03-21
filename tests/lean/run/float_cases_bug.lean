def foo (xs : List Nat) :=
xs.span (λ n, ↑(toBool (n = 1)))
