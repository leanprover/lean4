def foo (x : Nat) (h : x.succ < 0) : Bool := by
  contradiction
