def f (a : Array Nat) (i : Nat) (v : Nat) (h : i < a.size) : Array Nat :=
  a.set i (a.get i h + v)

set_option pp.proofs true

theorem ex1 (h₃ : i = j) : f a i (0 + v) h₁ = f a j v h₂ := by
  simp
  trace_state
  simp [h₃]

theorem ex2 (h₃ : i = j) : f a (0 + i) (0 + v) h₁ = f a j v h₂ := by
  simp
  trace_state
  simp [h₃]

theorem ex3 (h₃ : i = j) : f a (0 + i) (0 + v) h₁ = f a j v h₂ := by
  simp [h₃]
