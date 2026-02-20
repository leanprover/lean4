example (a b c d e f : Nat) (h : [a, b, c] = [d, e, f]) : a + b + c = d + e + f := by
  injections
  simp [*]
