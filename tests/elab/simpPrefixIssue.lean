universe u
axiom f {α : Sort u} (a : α) : α
axiom f_eq {α : Sort u} (a : α) : f a = a

example (a : Nat) : f id a = a := by
  simp only [f_eq]
  trace_state
  rfl
