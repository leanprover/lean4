set_option pp.analyze false

def p (x y : Nat) := x = y

example (x y : Nat) : p (x + y) (y + x + 0) := by
  conv =>
    whnf
    congr
    . skip
    . whnf; skip
  traceState
  rw [Nat.add_comm]
  rfl

example (x y : Nat) : p (x + y) (y + x + 0) := by
  conv =>
    whnf
    rhs
    whnf
  traceState
  rw [Nat.add_comm]
  rfl

example (x y : Nat) : p (x + y) (y + x + 0) := by
  conv =>
    whnf
    lhs
    whnf
  conv =>
    rhs
    whnf
  traceState
  apply Nat.add_comm x y

example (x y : Nat) : p (x + y) (0 + y + x) := by
  conv =>
    whnf
    rhs
    rw [Nat.zero_add, Nat.add_comm]
  rfl
