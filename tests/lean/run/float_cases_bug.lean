def foo (xs : List Nat) :=
xs.span (fun n => coe (decide (n = 1)))
