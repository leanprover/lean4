theorem test (p : Nat × Nat) : (match p with | (a, b) => a = b) → (p.1 = p.2) := by
  intro (h : (match p with | (a, b) => a = b))
  exact h
