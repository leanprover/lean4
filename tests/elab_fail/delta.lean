def f (x : Nat) : Nat := x + 1

example (x y : Nat) (h : f x = 0) : False := by
  delta f at h
  trace_state
  contradiction

example (x y : Nat) (h : f x = 0) : False := by
  delta f -- Error

example (x y : Nat) (h1 : f x = 0) (h2 : 0 = 0) : False := by
  delta f at h2 -- Error

example (x y : Nat) (h1 : f x = 0) (h2 : 0 = 0) : False := by
  delta f at h1 h2 -- Error

example (x y : Nat) (h1 : f x = 0) (h2 : 0 = 0) : False := by
  delta f at *
  trace_state
  contradiction

example (x y : Nat) (h2 : 0 = 0) : False := by
  delta f at *
