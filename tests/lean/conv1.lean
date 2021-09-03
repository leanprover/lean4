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

def f (x y z : Nat) : Nat :=
  y

example (x y : Nat) : f x (x + y + 0) y = y + x := by
  conv =>
    lhs
    arg 2
    whnf
  traceState
  simp [f]
  apply Nat.add_comm

example (x y : Nat) : f x (x + y + 0) y = y + x := by
  conv =>
    lhs
    arg 2
    change x + y
    traceState
    rw [Nat.add_comm]

example : id (fun x y => 0 + x + y) = Nat.add := by
  conv =>
    lhs
    arg 1
    funext a b
    traceState
    rw [Nat.zero_add]
    traceState

example : id (fun x y => 0 + x + y) = Nat.add := by
  conv =>
    enter [1, 1, a, b]
    traceState
    rw [Nat.zero_add]
