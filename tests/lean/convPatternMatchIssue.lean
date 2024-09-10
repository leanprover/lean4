def test : (λ x => x)
           =
           (λ x : Nat =>
             let_fun foo := λ y => id (id y)
             foo x) := by
  conv =>
    pattern (id _)
    trace_state
    skip
  rfl
