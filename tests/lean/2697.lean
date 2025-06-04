example (h : ∃ _ : Nat, P) : P := h.2

example (h : ∃ _ : Nat, P) : P := by
  let ⟨_, P⟩ := h
  exact P
