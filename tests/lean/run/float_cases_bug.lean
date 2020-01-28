def foo (xs : List Nat) :=
xs.span (fun n => oldCoe (decide (n = 1)))
