example : (λ (u : Nat) => u + 0) = id :=by
  conv =>
    lhs
    intro u
    change u
  rfl
