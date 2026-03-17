def f (n : Nat) := n + 1

example (k : Nat) (h : let x := 10; f x = k) : 11 = k := by
  have : f 10 = 11 := rfl
  conv at h => zeta; rw [this]
  trace_state
  exact h

example (k y : Nat) (h : let x := y; f (0+x) = k) : f y = k := by
  conv at h => ext x; lhs; arg 1; rw [Nat.zero_add]
  trace_state
  exact h

example (g : Nat → Nat) (y : Nat) (h : let x := y; g (0+x) = 0+x) : g y = 0 + y := by
  conv at h => enter [x, 1, 1]; rw [Nat.zero_add]
  trace_state
  exact h

example (g : Nat → Nat) (y : Nat) (h : let x := y; let z := y + 1; g (0+x) = 0+z) : g y = y + 1 := by
  conv at h => enter [x, z, 1, 1]; rw [Nat.zero_add]
  trace_state
  conv at h => enter [x, z, 2]; rw [Nat.zero_add]
  trace_state
  exact h
