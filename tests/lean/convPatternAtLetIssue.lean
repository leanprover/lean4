def f (x : Nat) := x

def test : (λ x => f x)
           =
           (λ x : Nat =>
             let foo := λ y => id (id y)
             foo x) := by
  conv =>
    pattern (id _)
    trace_state
    simp
    trace_state
