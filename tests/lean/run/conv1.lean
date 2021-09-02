set_option pp.analyze false

def p (x y : Nat) := x = y

example (x y : Nat) : p (x + y) (y + x + 0) := by
  conv =>
    whnf
    congr
    skip
    whnf
    skip
  traceState
  rw [Nat.add_comm]
  rfl
