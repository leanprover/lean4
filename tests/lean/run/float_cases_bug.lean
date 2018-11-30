def foo (xs : list nat) :=
xs.span (λ n, ↑(to_bool (n = 1)))
