

def foo (xs : List Nat) :=
xs.span (fun n => (decide (n = 1)))
