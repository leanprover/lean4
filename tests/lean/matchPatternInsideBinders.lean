def test : (λ x : Nat => id (id x)) = λ x => x := by
  conv in (id _) =>
    trace_state
    simp
