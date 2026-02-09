def g (x : Nat) := 2*x + 1

def f (x : Nat) : Nat :=
  match g x with
  | 0 => 1
  | y + 1 => g x

example : f x = 2*x + 1 := by
  unfold f
  split
  next h => simp +arith [g] at h
  next y h =>
    trace_state
    -- split tactic should *not* rewrite `g x` to `Nat.succ y`
    show g x = 2*x + 1
    simp [g]
