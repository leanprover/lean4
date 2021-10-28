def twice : Nat → Nat := λ n => 2*n

def foo1 : (λ x : Nat => id (twice (id x))) = twice := by
  conv in (id _) =>
    trace_state
    conv =>
      enter [1,1]
      trace_state
      simp
      trace_state
    trace_state  -- `id (twice x)`


theorem foo2 (y : Nat) : (fun x => x + y = 0) = (fun x => False) := by
  conv =>
    trace_state
    conv =>
      lhs
      trace_state
      intro x
      rw [Nat.add_comm]
      trace_state
    trace_state
  trace_state
  sorry
