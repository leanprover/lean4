def f (x : Nat) :=
  have y := x+1
  y+y

def g (x : Nat × Nat) :=
  have (y, z) := x
  y + y

theorem ex1 (h : p ∧ q ∧ r) : p := by
  have ⟨h', _, _⟩ := h
  exact h'

theorem ex2 (h : p ∧ q ∧ r) : p :=
  have ⟨h, _, _⟩ := h
  h

theorem ex3 (h : p ∧ q ∧ r) : r :=
  have ⟨_, _, h⟩ := h
  h
