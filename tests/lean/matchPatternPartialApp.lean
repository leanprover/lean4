def test2 : (Function.comp id id) = λ x : Nat => x := by
  conv in (Function.comp _) =>
    trace_state
    simp (config := { unfoldPartialApp := true }) [Function.comp, id]
    trace_state
