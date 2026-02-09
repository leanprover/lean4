opaque f (a b : Nat) : Nat
example : f 1 2 = f 2 1 := by
  generalize h : f 1 = g
  /- g : ℕ → ℕ
  h : f 1 = g
  ⊢ g 2 = f 2 1 -/
  trace_state
  sorry
