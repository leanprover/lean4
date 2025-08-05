def test : (λ x => x)
           =
           (λ x : Nat =>
             have foo := λ y => id (id y)
             foo x) := by
  conv =>
    pattern (id _)
    trace_state
    skip
  rfl
