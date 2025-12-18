opaque f (a : Nat) (h : a > 0) : Nat

example (h : a = b) : f (a + 1) (by simp +arith) = f (1 + b) (by simp +arith) := by
  conv => lhs; congr; rw [h]
  conv => lhs; congr; rw [Nat.add_comm]

opaque g (p : Prop) [Decidable p] (a : Nat) (h : a > 0) : Nat

example (h : a = b) : g True (a + 1) (by simp +arith) = g (1+1=2) (1 + b) (by simp +arith) := by
  conv =>
    lhs
    congr
    . rfl
    . rw [h]
  conv =>
    lhs
    congr
    . rfl
    . rw [Nat.add_comm]
  conv =>
    rhs
    congr
    . simp
    . rfl
